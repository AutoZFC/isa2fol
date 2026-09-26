import Reader

private let logic: Set = ["Pure", "IFOL", "FOL"]

private func layer(_ name: String) -> String { String(name.prefix { $0 != "." }) }

func surfaceReport(_ s: Surface, command: String) -> String {
    let total = s.named.values.reduce(0, +)
    var out: [String] = []
    func line(_ text: String = "") { out.append(text) }
    func percent(_ n: Int) -> String { total == 0 ? "-" : String(format: "%.1f%%", 100 * Double(n) / Double(total)) }
    func table(_ counts: [Item: Int], _ header: String, where keep: (Item) -> Bool, name: (Item) -> String) {
        let rows = counts.filter { keep($0.key) }.sorted { ($1.value, $0.key) < ($0.value, $1.key) }
        guard !rows.isEmpty else {
            line("(none)")
            return
        }
        line("| \(header) | theorems | % |")
        line("|---|---:|---:|")
        for (item, n) in rows { line("| `\(name(item))` | \(n) | \(percent(n)) |") }
    }
    let byName: (Item) -> String = { $0.name }

    line("# SOURCE SURFACE — what the isa dialect must model")
    line()
    line("**Generated — do not edit.** `\(command)`. A census, not mathematics:")
    line("`docs/FOUNDATION.md` says what the translation must satisfy; this says what the corpus contains.")
    line()
    line("**The cut.** The population is the NAMED theorems of the ZF sessions — unnamed boxes are pieces of")
    line("the proofs that reach them. A proof includes every unnamed box it reaches and stops at every named")
    line("theorem. A citation of a Pure/IFOL/FOL rule is a frontier leaf and takes with it the arguments that")
    line("discharge the rule's leading `OFCLASS` premises. A box's statement is a proposition inside its citer's")
    line("proof. Counts are theorems whose statement, or proof, contains the item.")
    line()
    line("## Population")
    line()
    line("| session | named theorems |")
    line("|---|---:|")
    for name in zfSessions { line("| \(name) | \(s.named[name].map(String.init) ?? "**not in the export**") |") }
    line("| **all** | **\(total)** |")
    line()
    line("## Statements")
    line()
    line("### Logical constants")
    line()
    table(s.statement, "constant", where: { $0.kind == .constant && logic.contains(layer($0.name)) }, name: byName)
    line()
    let zf = s.statement.keys.filter { $0.kind == .constant && !logic.contains(layer($0.name)) }.count
    line("Plus **\(zf) distinct ZF constants**.")
    line()
    line("### Types")
    line()
    table(s.statement, "type", where: { $0.kind == .type || $0.kind == .typeVariable },
          name: { $0.kind == .typeVariable ? "a type variable" : $0.name })
    line()
    line("### Other constructs")
    line()
    table(s.statement, "construct", where: { $0.kind == .ofclass || $0.kind == .schematic },
          name: { $0.kind == .ofclass ? "OFCLASS(_, \($0.name))" : "a schematic variable" })
    line()
    line("## Proofs")
    line()
    line("### Frontier — Pure/IFOL/FOL rules cited")
    line()
    for l in ["Pure", "IFOL", "FOL"] {
        line("#### \(l)")
        line()
        table(s.proof, "rule", where: { $0.kind == .theorem && layer($0.name) == l }, name: byName)
        line()
    }
    line("### Axioms")
    line()
    table(s.proof, "axiom", where: { $0.kind == .axiom }, name: byName)
    line()
    line("### Proof calculus")
    line()
    table(s.proof, "step", where: { $0.kind == .calculus }, name: byName)
    line()
    line("### Inside proofs — logical constants, types and constructs of the propositions")
    line()
    table(s.proof, "item", where: { item in
        switch item.kind {
        case .constant: return logic.contains(layer(item.name))
        case .typeVariable, .schematic, .ofclass, .oracle: return true
        case .type, .axiom, .theorem, .calculus: return false
        }
    }, name: { item in
        switch item.kind {
        case .typeVariable: return "a type variable"
        case .schematic: return "a schematic variable"
        case .ofclass: return "OFCLASS(_, \(item.name))"
        case .oracle: return "oracle \(item.name)"
        case .constant, .type, .axiom, .theorem, .calculus: return item.name
        }
    })
    line()
    line("**\(s.citedZF) distinct named ZF theorems are cited** by ZF proofs — ZF content, not the frontier.")
    line("**\(s.absorbed) class-premise discharges** were absorbed into the rule citations they belong to.")
    return out.joined(separator: "\n") + "\n"
}
