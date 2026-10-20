import FolDialect
import Foundation
import IR
import Lowering

/// Base's schemas Logic cites, parsed from base's own files into `t`.
func base(in t: inout Table) throws -> Base {
    let directory = URL(fileURLWithPath: #filePath).deletingLastPathComponent().deletingLastPathComponent()
        .deletingLastPathComponent().appendingPathComponent("base")
    return try Base(try parse(
        statements: BaseStatement.allCases.map(\.rawValue),
        from: try baseTexts(directory),
        in: &t,
    ))
}

/// `roots` lowered by `pass` as the one unit of its own run: built at `definitions`, nothing shared.
func run(
    _ pass: some Pass,
    _ roots: [NodeID],
    _ definitions: [Definition] = [],
    citing forms: [NodeID: NodeID] = [:],
    in t: inout Table,
) throws -> [NodeID] {
    var memo = Memo()
    return try pass.walk(definitions, in: &t).run(roots, citing: forms, sharing: &memo, in: &t)
}
