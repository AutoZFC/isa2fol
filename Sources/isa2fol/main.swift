import Foundation
import IR
import Reader

func fail(_ message: String, _ code: Int32) -> Never {
    FileHandle.standardError.write(Data((message + "\n").utf8))
    exit(code)
}

func kind(_ r: ReaderRefusal) -> String {
    switch r {
    case .typeConstructor: "typeConstructor"
    case .ofclass: "ofclass"
    case .betaRedex: "betaRedex"
    case .nameSegment: "nameSegment"
    case .omittedProof: "omittedProof"
    case .oracle: "oracle"
    }
}

func describe(_ error: any Error) -> String {
    guard let failure = error as? ReadFailure else { return "\(error)" }
    return "\(failure.file): \(describe(failure.error))"
}

func stopped(_ error: any Error) -> Never {
    fail("the read stopped at \(describe(error))", 1)
}

let arguments = Array(CommandLine.arguments.dropFirst())
let usage = """
    usage: isa2fol read EXPORT_DIR [--show OUTCOME]
           isa2fol lower EXPORT_DIR [--through STAGE] [--theorem NAME,…] [--skip SESSION,…] [--threads N] [--emit DIR]
           isa2fol surface EXPORT_DIR
           isa2fol closure EXPORT_DIR
    """

if arguments.count == 2, arguments[0] == "surface" || arguments[0] == "closure" {
    do {
        var reader = try Reader(try Export(root: arguments[1]))
        let census = try reader.census()
        let command = "isa2fol \(arguments[0]) \(arguments[1])"
        print(
            arguments[0] == "surface"
                ? surfaceReport(census, command: command)
                : closureReport(census, command: command),
            terminator: "",
        )
    } catch {
        stopped(error)
    }
    exit(0)
}

if arguments.first == "lower", arguments.count >= 2, arguments.count % 2 == 0 {
    var options = [String: String]()
    for k in stride(from: 2, to: arguments.count, by: 2) {
        guard
            ["--emit", "--through", "--theorem", "--skip", "--threads"].contains(arguments[k]),
            options.updateValue(arguments[k + 1], forKey: arguments[k]) == nil
        else { fail(usage, 2) }
    }
    guard
        let threads = Int(options["--threads"] ?? "\(ProcessInfo.processInfo.activeProcessorCount)"),
        threads > 0
    else { fail(usage, 2) }
    lower(arguments[1], Options(
        emit: options["--emit"],
        through: options["--through"],
        theorems: options["--theorem"].map { $0.split(separator: ",").map(String.init) },
        skip: options["--skip"].map { $0.split(separator: ",").map(String.init) } ?? [],
        threads: threads,
    ))
    exit(0)
}

guard arguments.count == 2 || (arguments.count == 4 && arguments[2] == "--show"), arguments[0] == "read" else {
    fail(usage, 2)
}

let show = arguments.count == 4 ? arguments[3] : nil

func label(_ outcome: Outcome) -> String {
    switch outcome {
    case .proved: "proved"
    case .refused(let r): "refused: " + kind(r)
    }
}

let start = Date()
var named = [String: [String: Int]]()
var cited = [String: Int]()
var boxes = [String: Int]()
var reader: Reader
do {
    reader = try Reader(try Export(root: arguments[1]))
    var read = Set<Theorem>()
    func outcome(_ theorem: Theorem) throws -> String {
        read.insert(theorem)
        let o = try reader.read(theorem)
        if label(o) == show || (show == "refused" && label(o).hasPrefix("refused")) {
            print("\(theorem)\t\(reader.name(of: theorem) ?? "-")\t\(o)")
        }
        return label(o)
    }
    for theorem in reader.population {
        named[session(of: theorem.theory)!, default: [:]][try outcome(theorem), default: 0] += 1
    }
    var next = 0
    while next < reader.cited.count {
        let theorem = reader.cited[next]
        next += 1
        guard !read.contains(theorem) else { continue }
        let o = try outcome(theorem)
        if reader.name(of: theorem) == nil { boxes[o, default: 0] += 1 } else { cited[o, default: 0] += 1 }
    }
} catch {
    stopped(error)
}

func report(_ title: String, _ counts: [String: Int]) {
    print("\(title): \(counts.values.reduce(0, +))")
    for key in counts.keys.sorted() { print("  \(key): \(counts[key]!)") }
}

report("named theorems, all ZF sessions", named.values.reduce(into: [:]) { $0.merge($1, uniquingKeysWith: +) })
for s in named.keys.sorted() { report("  \(s)", named[s]!) }
report("named theorems they cite outside the ZF sessions", cited)
report("boxes binding a proposition they cite", boxes)
print("table: \(reader.table.count) nodes; \(String(format: "%.1f", Date().timeIntervalSince(start))) s")
