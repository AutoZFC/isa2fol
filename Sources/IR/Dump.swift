extension Graph {
    public func dump() -> String {
        var out: [String] = []
        func line(_ id: OpID, _ depth: Int) {
            let pad = String(repeating: "  ", count: depth)
            let ops = op(id).operands.map(\.description).joined(separator: ", ")
            let args = ops.isEmpty ? "" : "(\(ops))"
            out.append("\(pad)\(id):\(type(of: id)) = \(op(id))\(args)")
            if let r = op(id).region { block(r, depth + 1) }
        }
        func block(_ r: RegionID, _ depth: Int) {
            let pad = String(repeating: "  ", count: depth)
            let a = region(r).args.map { "\($0):\(type(of: $0))" }.joined(separator: ", ")
            out.append("\(pad)\(r)(\(a)):")
            for id in region(r).ops where !isErased(id) { line(id, depth + 1) }
        }
        block(root, 0)
        return out.joined(separator: "\n")
    }
}
