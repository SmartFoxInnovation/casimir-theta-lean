using System.Collections;
using System.IO.MemoryMappedFiles;
using System.Text.Json;

static class ExportSlice
{
    private enum Kind { Name, Universe, Expression, Declaration }
    private readonly record struct Record(Kind Kind, ulong Id);

    public static void Run(string sourcePath, string index, string outputPath,
        string? declarationManifest = null, ulong start = 0, ulong finish = ulong.MaxValue,
        bool offsetsOnly = false)
    {
        using var source = new ReadMap(sourcePath);
        using var names = new ReadMap(Path.Combine(index, "names.u64"));
        using var levels = new ReadMap(Path.Combine(index, "levels.u64"));
        using var expressions = new ReadMap(Path.Combine(index, "expressions.u64"));
        using var pairs = new ReadMap(Path.Combine(index, "declarations.u64"));
        var baseIds = File.Exists(Path.Combine(index, "base-ids.u64")) ?
            ReadBaseIds(Path.Combine(index, "base-ids.u64")) : new HashSet<ulong>();
        var fullClosure = declarationManifest == null ? null : ReadBaseIds(declarationManifest);
        var roots = fullClosure == null ? JsonSerializer.Deserialize<Dictionary<string, ulong>>(
            File.ReadAllText(Path.Combine(index, "root-ids.json")))! : null;
        var declarationOffsets = new ulong[names.TableLength];
        for (int i = 0; i < pairs.TableLength; i += 2)
            declarationOffsets[pairs.At(i)] = pairs.At(i + 1);
        var tables = new[] { names, levels, expressions };
        var selected = tables.Select(table => new BitArray(table.TableLength)).ToArray();
        var declarations = new HashSet<ulong>();
        IEnumerable<ulong> rootIds = roots != null ? roots.Values :
            Enumerable.Range(1, declarationOffsets.Length - 1)
                .Where(id => declarationOffsets[id] >= start && declarationOffsets[id] < finish &&
                    fullClosure!.Contains(declarationOffsets[id]))
                .Select(id => (ulong)id);
        var queue = new Stack<Record>(rootIds.Select(root => new Record(Kind.Declaration, root)));
        long count = 1;
        while (queue.TryPop(out Record record))
        {
            ulong offset;
            if (record.Kind == Kind.Declaration)
            {
                if (baseIds.Contains(record.Id))
                    continue;
                offset = declarationOffsets[record.Id];
                if (offset == 0)
                    throw new InvalidDataException($"Missing declaration with export name ID {record.Id}");
                if (fullClosure != null)
                {
                    if (!fullClosure.Contains(offset) || offset >= finish)
                        throw new InvalidDataException($"A batch has an unexpected forward dependency at byte {offset}");
                    if (offset < start)
                        continue;
                }
                if (!declarations.Add(offset))
                    continue;
            }
            else
            {
                if (record.Id == 0 && record.Kind != Kind.Expression)
                    continue;
                int kind = (int)record.Kind;
                int identifier = checked((int)record.Id);
                if (selected[kind][identifier])
                    continue;
                selected[kind][identifier] = true;
                offset = tables[kind].At(identifier);
                if (offset == 0)
                    throw new InvalidDataException($"Missing {record.Kind} ID {record.Id}");
            }
            if (++count % 10_000_000 == 0)
                Console.WriteLine($"Selected {count:N0} proof rows");
            var row = new Utf8JsonReader(source.Row(offset));
            using var json = JsonDocument.ParseValue(ref row);
            var fields = json.RootElement;
            switch (record.Kind)
            {
                case Kind.Name:
                    var name = fields.TryGetProperty("str", out var str) ? str : fields.GetProperty("num");
                    Push(queue, Kind.Name, name.GetProperty("pre"));
                    break;
                case Kind.Universe:
                    foreach (var field in fields.EnumerateObject())
                    {
                        switch (field.Name)
                        {
                            case "il": break;
                            case "param": Push(queue, Kind.Name, field.Value); break;
                            case "succ": Push(queue, Kind.Universe, field.Value); break;
                            case "max":
                            case "imax": PushList(queue, Kind.Universe, field.Value); break;
                            default: throw new InvalidDataException($"Unsupported universe {field.Name}");
                        }
                    }
                    break;
                case Kind.Expression:
                    AddExpression(queue, fields);
                    break;
                case Kind.Declaration:
                    var declaration = fields.EnumerateObject().First();
                    if (declaration.Name == "inductive")
                    {
                        foreach (var member in declaration.Value.EnumerateObject())
                            foreach (var item in member.Value.EnumerateArray())
                                AddDeclaration(queue, item);
                    }
                    else
                        AddDeclaration(queue, declaration.Value);
                    break;
            }
        }
        if (offsetsOnly)
        {
            WriteOffsets(outputPath, declarations);
            Console.WriteLine($"Selected {declarations.Count:N0} declaration offsets");
            return;
        }

        string staging = outputPath + ".part";
        using (var output = new FileStream(staging, FileMode.Create, FileAccess.Write, FileShare.None, 4 * 1024 * 1024))
        {
            output.Write(source.Row(0));
            var streams = tables.Select((table, i) => ActiveOffsets(table, selected[i])).ToList();
            streams.Add(declarations.Order());
            var merge = new PriorityQueue<IEnumerator<ulong>, ulong>();
            foreach (var sequence in streams)
            {
                var cursor = sequence.GetEnumerator();
                if (cursor.MoveNext())
                    merge.Enqueue(cursor, cursor.Current);
                else
                    cursor.Dispose();
            }
            while (merge.TryDequeue(out var cursor, out ulong offset))
            {
                output.Write(source.Row(offset));
                if (cursor.MoveNext())
                    merge.Enqueue(cursor, cursor.Current);
                else
                    cursor.Dispose();
            }
        }
        File.Move(staging, outputPath, overwrite: true);
        if (fullClosure == null)
            WriteOffsets(outputPath + ".declarations.u64", declarations);
        string description = roots != null ? string.Join(", ", roots.Keys) : $"batch [{start}, {finish})";
        Console.WriteLine($"Selected {count:N0} export rows for {description}");
    }

    private static void WriteOffsets(string path, HashSet<ulong> declarations)
    {
        using var offsets = new BinaryWriter(new BufferedStream(File.Create(path)));
        foreach (ulong offset in declarations.Order())
            offsets.Write(offset);
    }

    private static IEnumerable<ulong> ActiveOffsets(ReadMap table, BitArray selected)
    {
        for (int i = 0; i < selected.Length; i++)
            if (selected[i])
                yield return table.At(i);
    }

    private static HashSet<ulong> ReadBaseIds(string file)
    {
        var ids = new HashSet<ulong>();
        using var stream = File.OpenRead(file);
        using var reader = new BinaryReader(stream);
        while (stream.Position < stream.Length)
            ids.Add(reader.ReadUInt64());
        return ids;
    }

    private static void Push(Stack<Record> queue, Kind kind, JsonElement element) =>
        queue.Push(new Record(kind, element.GetUInt64()));

    private static void PushList(Stack<Record> queue, Kind kind, JsonElement items)
    {
        foreach (var element in items.EnumerateArray())
            Push(queue, kind, element);
    }

    private static void AddDeclaration(Stack<Record> queue, JsonElement term)
    {
        foreach (var field in term.EnumerateObject())
        {
            switch (field.Name)
            {
                case "name":
                case "induct": Push(queue, Kind.Name, field.Value); break;
                case "levelParams":
                case "all":
                case "ctors": PushList(queue, Kind.Name, field.Value); break;
                case "type":
                case "value": Push(queue, Kind.Expression, field.Value); break;
                case "rules":
                    foreach (var rule in field.Value.EnumerateArray())
                    {
                        Push(queue, Kind.Name, rule.GetProperty("ctor"));
                        Push(queue, Kind.Expression, rule.GetProperty("rhs"));
                    }
                    break;
            }
        }
    }

    private static void AddExpression(Stack<Record> queue, JsonElement fields)
    {
        foreach (var field in fields.EnumerateObject())
        {
            var item = field.Value;
            switch (field.Name)
            {
                case "ie":
                case "bvar":
                case "natVal":
                case "strVal": break;
                case "const":
                    var name = item.GetProperty("name");
                    Push(queue, Kind.Declaration, name);
                    Push(queue, Kind.Name, name);
                    PushList(queue, Kind.Universe, item.GetProperty("us"));
                    break;
                case "sort":
                    Push(queue, Kind.Universe, item);
                    break;
                case "app":
                    Push(queue, Kind.Expression, item.GetProperty("fn"));
                    Push(queue, Kind.Expression, item.GetProperty("arg"));
                    break;
                case "forallE":
                case "lam":
                case "letE":
                    Push(queue, Kind.Name, item.GetProperty("name"));
                    Push(queue, Kind.Expression, item.GetProperty("type"));
                    Push(queue, Kind.Expression, item.GetProperty("body"));
                    if (field.Name == "letE")
                        Push(queue, Kind.Expression, item.GetProperty("value"));
                    break;
                case "proj":
                    var structure = item.GetProperty("typeName");
                    Push(queue, Kind.Declaration, structure);
                    Push(queue, Kind.Name, structure);
                    Push(queue, Kind.Expression, item.GetProperty("struct"));
                    break;
                case "mdata":
                    Push(queue, Kind.Expression, item.GetProperty("expr"));
                    break;
                default: throw new InvalidDataException($"Unsupported expression {field.Name}");
            }
        }
    }

    private sealed unsafe class ReadMap : IDisposable
    {
        private readonly MemoryMappedFile map;
        private readonly MemoryMappedViewAccessor view;
        private readonly byte* data;
        private readonly long length;

        public ReadMap(string path)
        {
            length = new FileInfo(path).Length;
            map = MemoryMappedFile.CreateFromFile(path, FileMode.Open, null, 0, MemoryMappedFileAccess.Read);
            view = map.CreateViewAccessor(0, 0, MemoryMappedFileAccess.Read);
            byte* pointer = null;
            view.SafeMemoryMappedViewHandle.AcquirePointer(ref pointer);
            data = pointer + view.PointerOffset;
        }

        public int TableLength => checked((int)(length / sizeof(ulong)));

        public ulong At(int index)
        {
            if (index < 0 || index >= TableLength)
                throw new IndexOutOfRangeException($"Invalid table ID {index}");
            return ((ulong*)data)[index];
        }

        public ReadOnlySpan<byte> Row(ulong position)
        {
            if (position >= (ulong)length)
                throw new IndexOutOfRangeException($"Invalid proof offset {position}");
            int count = (int)Math.Min(length - (long)position, 32 * 1024 * 1024);
            var span = new ReadOnlySpan<byte>(data + position, count);
            int end = span.IndexOf((byte)'\n');
            if (end < 0)
                throw new InvalidDataException($"Incomplete proof row at byte {position}");
            return span[..(end + 1)];
        }

        public void Dispose()
        {
            view.SafeMemoryMappedViewHandle.ReleasePointer();
            view.Dispose();
            map.Dispose();
        }
    }
}
