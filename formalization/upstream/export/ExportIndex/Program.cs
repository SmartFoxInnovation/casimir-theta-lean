using System.Buffers.Text;
using System.Text.Json;

if (args.Length == 4 && args[0] == "select")
{
    ExportSlice.Run(args[1], args[2], args[3]);
    return;
}

if (args.Length == 4 && args[0] == "closure")
{
    ExportSlice.Run(args[1], args[2], args[3], offsetsOnly: true);
    return;
}
if (args.Length == 7 && args[0] == "batch-select")
{
    ExportSlice.Run(args[1], args[2], args[3], args[4], ulong.Parse(args[5]), ulong.Parse(args[6]));
    return;
}

if (args.Length != 2 && args.Length < 4)
    throw new ArgumentException("Usage: ExportIndex input.ndjson index-directory [base-names.ndjson root ...]");

const int bufferSize = 32 * 1024 * 1024;
Directory.CreateDirectory(args[1]);
using var input = new FileStream(args[0], FileMode.Open, FileAccess.Read, FileShare.Read,
    bufferSize: 1, FileOptions.SequentialScan);
using var names = NewTable(args[1], "names.u64");
using var levels = NewTable(args[1], "levels.u64");
using var expressions = NewTable(args[1], "expressions.u64");
using var declarations = NewTable(args[1], "declarations.u64");
using var selectedNames = args.Length >= 4 ? new NameSelection(args[1], args[2], args[3..]) : null;
names.Write(0UL);
levels.Write(0UL);
ulong nameCount = 1, levelCount = 1, expressionCount = 0, declarationCount = 0;
ulong offset = 0;
long nextReport = 8L * 1024 * 1024 * 1024;
var buffer = new byte[bufferSize];
int cursor = 0;
int available = 0;
while (true)
{
    int length = buffer.AsSpan(cursor, available - cursor).IndexOf((byte)'\n');
    if (length < 0)
    {
        int remaining = available - cursor;
        if (remaining == buffer.Length)
            throw new InvalidDataException($"Oversized export record at byte {offset}");
        buffer.AsSpan(cursor, remaining).CopyTo(buffer);
        int read = input.Read(buffer.AsSpan(remaining));
        if (read == 0)
        {
            if (remaining != 0)
                throw new InvalidDataException($"Incomplete export record at byte {offset}");
            break;
        }
        cursor = 0;
        available = remaining + read;
        continue;
    }
    var line = buffer.AsSpan(cursor, length);
    if (offset == 0)
    {
        if (!line.StartsWith("{\"meta\":"u8))
            throw new InvalidDataException("Export header missing");
    }
    else if (line.StartsWith("{\"in\":"u8))
    {
        selectedNames?.Accept(line, nameCount);
        WriteOffset(names, line[6..], offset, ref nameCount);
    }
    else if (line.StartsWith("{\"il\":"u8))
        WriteOffset(levels, line[6..], offset, ref levelCount);
    else if (line.StartsWith("{\"def\":"u8) || line.StartsWith("{\"thm\":"u8) ||
        line.StartsWith("{\"inductive\":"u8) || line.StartsWith("{\"opaque\":"u8) ||
        line.StartsWith("{\"axiom\":"u8) || line.StartsWith("{\"quot\":"u8))
    {
        var json = new Utf8JsonReader(line);
        bool found = false;
        while (json.Read())
        {
            if (json.TokenType != JsonTokenType.PropertyName || !json.ValueTextEquals("name"u8))
                continue;
            if (!json.Read() || !json.TryGetUInt64(out ulong id) || id == 0 || id >= nameCount)
                throw new InvalidDataException($"Invalid declaration name at byte {offset}");
            declarations.Write(id);
            declarations.Write(offset);
            declarationCount++;
            found = true;
        }
        if (!found)
            throw new InvalidDataException($"Declaration name missing at byte {offset}");
    }
    else
    {
        int field = line.IndexOf("\"ie\":"u8);
        if (field < 0)
            throw new InvalidDataException($"Unknown export record at byte {offset}");
        WriteOffset(expressions, line[(field + 5)..], offset, ref expressionCount);
    }
    cursor += length + 1;
    offset += (ulong)length + 1;
    if (offset >= (ulong)nextReport)
    {
        Console.WriteLine($"Indexed {offset:N0}/{input.Length:N0} bytes");
        nextReport += 8L * 1024 * 1024 * 1024;
    }
}
Console.WriteLine($"Indexed {nameCount:N0} names, {levelCount:N0} levels, {expressionCount:N0} expressions, and {declarationCount:N0} declaration entries");
selectedNames?.Finish();

static BinaryWriter NewTable(string folder, string name) =>
    new(new BufferedStream(File.Create(Path.Combine(folder, name)), 1024 * 1024));

static void WriteOffset(BinaryWriter table, ReadOnlySpan<byte> number, ulong offset, ref ulong expected)
{
    if (!Utf8Parser.TryParse(number, out ulong id, out int used) || id != expected ||
        used >= number.Length || (number[used] != (byte)',' && number[used] != (byte)'}'))
        throw new InvalidDataException($"Nonsequential export ID, expected {expected} at byte {offset}");
    table.Write(offset);
    expected++;
}

sealed class NameSelection : IDisposable
{
    private readonly string folder;
    private readonly Dictionary<(int Parent, bool Numeric, string Segment), int> trie = new();
    private readonly HashSet<int> baseNames = new();
    private readonly Dictionary<int, string> targets = new();
    private readonly Dictionary<string, ulong> found = new();
    private readonly List<int> prefixNodes = new() { 0 };
    private readonly BinaryWriter baseIds;

    public NameSelection(string folder, string basePath, string[] roots)
    {
        this.folder = folder;
        baseIds = new BinaryWriter(new BufferedStream(File.Create(Path.Combine(folder, "base-ids.u64"))));
        if (basePath != "-")
        {
            foreach (string row in File.ReadLines(basePath))
            {
                using var document = JsonDocument.Parse(row);
                int node = 0;
                foreach (var part in document.RootElement.EnumerateArray())
                {
                    bool numeric = part.ValueKind == JsonValueKind.Number;
                    node = Intern(node, numeric, numeric ? part.GetRawText() : part.GetString()!);
                }
                baseNames.Add(node);
            }
        }
        foreach (string root in roots)
        {
            int node = 0;
            foreach (string part in root.Split('.'))
                node = Intern(node, false, part);
            targets.Add(node, root);
        }
    }

    private int Intern(int parent, bool numeric, string segment)
    {
        var key = (parent, numeric, segment);
        if (trie.TryGetValue(key, out int node))
            return node;
        node = trie.Count + 1;
        trie.Add(key, node);
        return node;
    }

    public void Accept(ReadOnlySpan<byte> line, ulong id)
    {
        var json = new Utf8JsonReader(line);
        int parent = -1;
        bool numeric = false;
        int segmentStart = -1, segmentLength = 0;
        while (json.Read())
        {
            if (json.TokenType != JsonTokenType.PropertyName || json.CurrentDepth != 2)
                continue;
            if (json.ValueTextEquals("pre"u8))
            {
                if (!json.Read() || !json.TryGetInt32(out parent) || parent < 0 || parent >= prefixNodes.Count)
                    throw new InvalidDataException($"Invalid name parent for {id}");
            }
            else if (json.ValueTextEquals("str"u8) || json.ValueTextEquals("i"u8))
            {
                if (!json.Read())
                    throw new InvalidDataException($"Incomplete name part for {id}");
                numeric = json.TokenType == JsonTokenType.Number;
                segmentStart = checked((int)json.TokenStartIndex);
                segmentLength = checked((int)json.BytesConsumed) - segmentStart;
            }
        }
        if (parent < 0 || segmentStart < 0)
            throw new InvalidDataException($"Incomplete name record for {id}");
        int node = -1;
        int parentNode = prefixNodes[parent];
        if (parentNode >= 0)
        {
            var segment = line.Slice(segmentStart, segmentLength);
            string text = numeric ? System.Text.Encoding.UTF8.GetString(segment) : JsonSerializer.Deserialize<string>(segment)!;
            if (!trie.TryGetValue((parentNode, numeric, text), out node))
                node = -1;
        }
        prefixNodes.Add(node);
        if (targets.TryGetValue(node, out string? root))
            found.Add(root, id);
        if (baseNames.Contains(node))
            baseIds.Write(id);
    }

    public void Finish()
    {
        if (found.Count != targets.Count)
            throw new InvalidDataException("Roots missing from export: " +
                string.Join(", ", targets.Values.Where(n => !found.ContainsKey(n))));
        File.WriteAllText(Path.Combine(folder, "root-ids.json"), JsonSerializer.Serialize(found));
    }

    public void Dispose() => baseIds.Dispose();
}
