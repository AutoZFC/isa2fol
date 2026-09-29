import Foundation
import IR
import Reader

func fail(_ message: String, _ code: Int32) -> Never {
    FileHandle.standardError.write(Data((message + "\n").utf8))
    exit(code)
}

func kind(_ r: ReaderRefusal) -> String {
    switch r {
    case .typeConstructor: return "typeConstructor"
    case .ofclass: return "ofclass"
    case .betaRedex: return "betaRedex"
    case .nameSegment: return "nameSegment"
    case .omittedProof: return "omittedProof"
    case .oracle: return "oracle"
    }
}

func describe(_ error: any Error) -> String {
    guard let failure = error as? ReadFailure else { return "\(error)" }
    return "\(failure.file): \(describe(failure.error))"
}

let arguments = Array(CommandLine.arguments.dropFirst())
let usage = """
    usage: isa2fol read EXPORT_DIR [--show OUTCOME]
           isa2fol lower EXPORT_DIR
           isa2fol surface EXPORT_DIR
           isa2fol closure EXPORT_DIR
    """

if arguments.count == 2, arguments[0] == "surface" || arguments[0] == "closure" {
    do {
        var export = try Export(root: arguments[1])
        let command = "isa2fol \(arguments[0]) \(arguments[1])"
        print(arguments[0] == "surface" ? surfaceReport(try export.surface(), command: command)
                                        : closureReport(try export.closure(), command: command), terminator: "")
    } catch {
        fail("malformed export at \(describe(error))", 1)
    }
    exit(0)
}

if arguments.count == 2, arguments[0] == "lower" {
    lower(arguments[1])
    exit(0)
}

guard arguments.count == 2 || (arguments.count == 4 && arguments[2] == "--show"), arguments[0] == "read" else {
    fail(usage, 2)
}
let show = arguments.count == 4 ? arguments[3] : nil

func label(_ outcome: Outcome) -> String {
    switch outcome {
    case .proved: return "proved"
    case let .refused(r): return "refused: " + kind(r)
    }
}

let start = Date()
var named: [String: [String: Int]] = [:], cited: [String: Int] = [:]
var reader: Reader
do {
    reader = try Reader(try Export(root: arguments[1]))
    var read: Set<Theorem> = []
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
        if !read.contains(theorem) { cited[try outcome(theorem), default: 0] += 1 }
    }
} catch {
    fail("malformed export at \(describe(error))", 1)
}

func report(_ title: String, _ counts: [String: Int]) {
    print("\(title): \(counts.values.reduce(0, +))")
    for key in counts.keys.sorted() { print("  \(key): \(counts[key]!)") }
}

report("named theorems, all ZF sessions", named.values.reduce(into: [:]) { $0.merge($1, uniquingKeysWith: +) })
for s in named.keys.sorted() { report("  \(s)", named[s]!) }
report("named theorems they cite outside the ZF sessions", cited)
print("table: \(reader.table.count) nodes; \(String(format: "%.1f", Date().timeIntervalSince(start))) s")
