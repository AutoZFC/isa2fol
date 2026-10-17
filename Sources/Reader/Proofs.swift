import YXML

struct Citation: Hashable {
    let theory: String
    let serial: Int
    let name: String
    let index: Int
    let types: [IsaType]
}

enum ProofHead {
    case nop
    case bound(Int)
    case termAbstraction(IsaType, Body)
    case hypothesisAbstraction(Body, Body)
    case hypothesis(Body)
    case axiom(String, [IsaType])
    case ofclass(IsaType, String)
    case oracle(String, [IsaType])
    case theorem(Citation)
}

enum ProofArgument {
    case term(Body)
    case proof(Body)
}

enum ProofNode {
    case head(ProofHead)
    case application(Body, ProofArgument)
}

struct ProofSpine {
    let head: Body
    let node: ProofHead
    let arguments: [ProofArgument]
}

extension Decode {
    func proofNode(_ body: Body) throws -> ProofNode {
        try variant([
            { a, ts in
                try noAtoms(a)
                try emptyBody(ts)
                return .head(.nop)
            },
            { a, ts in
                try noAtoms(a)
                return .head(.bound(try Decode.int(try string(ts))))
            },
            { a, ts in
                _ = try one(a)
                let (T, p) = try pair(type, { $0 }, ts)
                return .head(.termAbstraction(T, p))
            },
            { a, ts in
                _ = try one(a)
                let (t, p) = try pair({ $0 }, { $0 }, ts)
                return .head(.hypothesisAbstraction(t, p))
            },
            { a, ts in
                try noAtoms(a)
                let (p, t) = try pair({ $0 }, { $0 }, ts)
                return .application(p, .term(t))
            },
            { a, ts in
                try noAtoms(a)
                let (p, q) = try pair({ $0 }, { $0 }, ts)
                return .application(p, .proof(q))
            },
            { a, ts in
                try noAtoms(a)
                return .head(.hypothesis(ts))
            },
            { a, ts in .head(.axiom(try one(a), try list(type, ts))) },
            { a, ts in .head(.ofclass(try type(ts), try one(a))) },
            { a, ts in .head(.oracle(try one(a), try list(type, ts))) },
            { a, ts in
                guard a.count == 4 else { throw MalformedExport.atoms(a) }
                return .head(.theorem(Citation(
                    theory: a[1],
                    serial: try Decode.int(a[0]),
                    name: a[2],
                    index: try Decode.int(a[3]),
                    types: try list(type, ts),
                )))
            },
        ], body)
    }

    func proofSpine(_ body: Body) throws -> ProofSpine {
        var arguments = [ProofArgument]()
        var head = body
        while true {
            switch try proofNode(head) {
            case .application(let function, let argument):
                arguments.append(argument)
                head = function

            case .head(let node):
                return ProofSpine(head: head, node: node, arguments: arguments.reversed())
            }
        }
    }
}
