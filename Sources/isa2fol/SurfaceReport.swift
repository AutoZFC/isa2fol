import IR
import Reader

private func population(_ c: Census, _ line: (String) -> Void) {
    line("| session | named theorems |")
    line("|---|---:|")
    for name in zfSessions { line("| \(name) | \(c.named[name].map(String.init) ?? "**not in the export**") |") }
    line("| **all** | **\(c.named.values.reduce(0, +))** |")
    line("")
    let refused = c.refused.values.reduce(0, +)
    line(refused == 0 ? "The reader refuses none of them, nor any theorem they cite."
                      : "The reader refuses \(refused), whose proofs are not followed: "
                        + c.refused.map { "\(kind($0.key)) \($0.value)" }.sorted().joined(separator: ", ") + ".")
}

private func percent(_ n: Int, of c: Census) -> String {
    String(format: "%.1f%%", 100 * Double(n) / Double(c.named.values.reduce(0, +)))
}

func surfaceReport(_ c: Census, command: String) -> String {
    var out: [String] = []
    func line(_ text: String) { out.append(text) }
    line("# SOURCE SURFACE — the patterns the translation owes a rule each")
    line("")
    line("**Generated — do not edit.** `\(command)`. A census, not mathematics: `docs/FOUNDATION.md` says what the")
    line("translation must satisfy; this lists what the corpus is built from, as the reader emits it — each pattern a")
    line("primitive at its type (`DESIGN.md` §4.3b). With one rule per pattern, every theorem built from them translates.")
    line("")
    line("- **The population** is the closure of the named ZF theorems: every theorem they cite, each read from its own")
    line("  proof, and the definition of every constant that occurs, transitively. An unnamed box is part of its citer's")
    line("  proof.")
    line("- **A count** is the named ZF theorems whose closure holds the pattern: the theorems that do not translate until")
    line("  it has a rule. A count orders the work; it never justifies a rule.")
    line("")
    line("## Population")
    line("")
    population(c, line)
    line("")
    line("## Patterns (\(c.patterns.count))")
    line("")
    line("| pattern | theorems | % |")
    line("|---|---:|---:|")
    for (p, n) in c.patterns.map({ ("\($0.key)", $0.value) }).sorted(by: { $0.0 < $1.0 }) {
        line("| `\(p)` | \(n) | \(percent(n, of: c)) |")
    }
    return out.joined(separator: "\n") + "\n"
}

func closureReport(_ c: Census, command: String) -> String {
    var out: [String] = []
    func line(_ text: String) { out.append(text) }
    func table(_ header: String, _ rows: [(String, Int)]) {
        guard !rows.isEmpty else {
            line("(none)")
            return
        }
        line("| \(header) | theorems reaching it | % |")
        line("|---|---:|---:|")
        for (name, n) in rows.sorted(by: { ($1.1, $0.0) < ($0.1, $1.0) }) { line("| `\(name)` | \(n) | \(percent(n, of: c)) |") }
    }
    var axioms: [Family: [(String, Int)]] = [:], definitions: [Family: [(String, Int)]] = [:], theory: [(String, Int)] = []
    for (cited, n) in c.citations {
        switch cited {
        case let .axiom(a): axioms[a.family, default: []].append((a.name, n))
        case let .isaDefinition(name, d): definitions[d.family, default: []].append((name, n))
        case let .theoryAxiom(name): theory.append((name, n))
        case .theorem, .lemma: break
        }
    }

    line("# CLOSURE — what every named ZF theorem rests on")
    line("")
    line("**Generated.** `\(command)`. Each named theorem of the ZF sessions is followed through every citation — named")
    line("theorems, derived Pure/IFOL/FOL rules, unnamed boxes, class discharges — down to axioms. A citation is read as")
    line("the reader types it (`DESIGN.md` §4.3b): an axiom of the foundation, a definition, or an axiom a theory above")
    line("the foundation states. Counts are named theorems whose closure contains it.")
    line("")
    population(c, line)
    for f in [Family.pure, .ifol, .fol] {
        line("")
        line("## \(f) — every axiom and definition reached")
        line("")
        table("axiom", (axioms[f] ?? []) + (definitions[f] ?? []))
    }
    line("")
    line("## zf — every axiom reached")
    line("")
    table("axiom", axioms[.zf] ?? [])
    line("")
    let zf = (definitions[.zf] ?? []).sorted { ($1.1, $0.0) < ($0.1, $1.0) }
    line("Plus **\(zf.count) definitions** of the zf family; the most-reached is reached by "
         + (zf.first.map { "\($0.1) (`\($0.0)`)" } ?? "none") + ".")
    line("")
    line("## Axioms of theories above the foundation — not ZF's")
    line("")
    table("axiom", theory)
    line("")
    line("## Type variables")
    line("")
    line("**\(c.polymorphic) named theorems state a type variable.** A citation at a type variable its citing proof does not")
    line("bind stops the read (`undeclaredTypeVariable`), so every instance is determined by its citer.")
    return out.joined(separator: "\n") + "\n"
}
