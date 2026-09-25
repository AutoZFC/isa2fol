import Foundation
import IR
import Reader

func fail(_ message: String, _ code: Int32) -> Never {
    FileHandle.standardError.write(Data((message + "\n").utf8))
    exit(code)
}

func kind(_ r: ReaderRefusal) -> String {
    switch r {
    case .typeVariable: return "typeVariable"
    case .prop: return "prop"
    case .typeConstructor: return "typeConstructor"
    case .schematicVariable: return "schematicVariable"
    case .ofclass: return "ofclass"
    case .pureInternal: return "pureInternal"
    case .betaRedex: return "betaRedex"
    case .quantifierOverFunction: return "quantifierOverFunction"
    case .nameSegment: return "nameSegment"
    }
}

let arguments = Array(CommandLine.arguments.dropFirst())
let usage = "usage: isa2fol statements EXPORT_DIR [--show REFUSAL]"
guard arguments.count == 2 || (arguments.count == 4 && arguments[2] == "--show"), arguments[0] == "statements" else {
    fail(usage, 2)
}
let show = arguments.count == 4 ? arguments[3] : nil

var all: [String: Int] = [:], named: [String: Int] = [:]
do {
    var export = try Export(root: arguments[1])
    for theory in export.theories {
        var t = Table()
        for read in try export.statements(theory, into: &t) {
            let key: String
            switch read.outcome {
            case .translated: key = "translated"
            case let .refused(r):
                key = "refused: " + kind(r)
                if kind(r) == show { print("\(theory)/proofs/\(read.serial)\t\(read.name ?? "-")\t\(r)") }
            }
            all[key, default: 0] += 1
            if read.name != nil, theory == "ZF" || theory.hasPrefix("ZF.") { named[key, default: 0] += 1 }
        }
    }
} catch let failure as ReadFailure {
    fail("malformed export at \(failure.file): \(failure.error)", 1)
}

for (title, counts) in [("named ZF theorems", named), ("all proof files", all)] {
    print("\(title): \(counts.values.reduce(0, +))")
    for key in counts.keys.sorted() { print("  \(key): \(counts[key]!)") }
}
