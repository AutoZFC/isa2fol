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
