import IR
import Testing
@testable import Lowering

/// Each request maps every ID it holds and nothing else: mapped, it visits exactly its IDs; mapped by a permutation and
/// back, it is itself (DESIGN "Memory — a unit of work's nodes leave with it", 2).
@Test
func eachRequestRemapsEveryIDItHolds() throws {
    var t = Table()
    let ids = try (0..<4).map { try t.intern(.isaFree("x\($0)", .i)) }
    let requests: [(any Request, [NodeID])] = [
        (AxiomFact(axiom: .extension, stated: ids[0], statement: ids[1]), [ids[0], ids[1]]),
        (Existence(term: ids[0], types: [.i], name: "EX"), [ids[0]]),
        (Uniqueness(term: ids[0], types: [.i], name: "UNIQ"), [ids[0]]),
        (ConstantFact(constant: .primitive(.zf(.pow)), type: .fn(.i, .i), fact: .classExists), []),
        (Unfolding(constant: Defined(.zf, "T.c", .object), statement: ids[0]), [ids[0]]),
        (LambdaFact(lambda: ids[0], types: [.i], fact: .classExists, name: "CLASS"), [ids[0]]),
        (RekeyFact(width: 2), []),
        (TupleFact(arity: 2, fact: .row), []),
        (Meeting(formula: ids[0], types: [.i], moving: .closed, keep: [], toValues: true, name: "MEET"), [ids[0]]),
        (
            Instantiation(
                formula: ids[0],
                lambda: ids[1],
                types: [.i],
                variable: 0,
                stated: false,
                forward: true,
                name: "BETA",
            ),
            [ids[0], ids[1]],
        ),
        (Arguments(lambda: ids[0], types: [.i], name: "ARGS"), [ids[0]]),
        (Leibniz(formula: ids[0], types: [.i], variable: 0, name: "SUBST"), [ids[0]]),
    ]
    let swap = Dictionary(uniqueKeysWithValues: zip(ids, ids.reversed()))
    for (r, held) in requests {
        var seen = [NodeID]()
        let same = r.remapped { x in
            seen.append(x)
            return x
        }
        #expect(seen == held, "\(r.name)")
        #expect(AnyHashable(same) == AnyHashable(r), "\(r.name)")
        let swapped = r.remapped { swap[$0]! }
        #expect(AnyHashable(swapped.remapped { swap[$0]! }) == AnyHashable(r), "\(r.name)")
        #expect(held.isEmpty || AnyHashable(swapped) != AnyHashable(r), "\(r.name)")
    }
}
