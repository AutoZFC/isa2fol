extension Graph {
    public func dump() -> String {
        var out: [String] = []
        func line(_ id: OpID, _ depth: Int) {
            let n = node(id)
            let res = n.results.map { "\($0):\(type(of: $0))" }.joined(separator: ", ")
            let ops = n.operands.map(\.description).joined(separator: ", ")
            out.append(String(repeating: "  ", count: depth)
                + (res.isEmpty ? "" : "\(res) = ") + "\(n.op)"
                + (ops.isEmpty ? "" : "(\(ops))"))
            for r in n.regions { block(r, depth + 1) }
        }
        func block(_ r: RegionID, _ depth: Int) {
            let args = region(r).args.map { "\($0):\(type(of: $0))" }.joined(separator: ", ")
            out.append(String(repeating: "  ", count: depth) + "\(r)(\(args)):")
            for id in region(r).ops where !node(id).erased { line(id, depth + 1) }
        }
        block(root, 0)
        return out.joined(separator: "\n")
    }
}
