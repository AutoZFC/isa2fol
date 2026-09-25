struct HashIndex: Sendable {
    private struct Slot: Sendable {
        var hash: Int
        var payload: Int32
    }

    private static let empty = Slot(hash: 0, payload: -1)
    private var slots = [Slot](repeating: empty, count: 1 << 10)
    private var count = 0

    func find(_ hash: Int, _ matches: (Int32) -> Bool) -> Int32? {
        let mask = slots.count - 1
        var i = hash & mask
        while slots[i].payload >= 0 {
            if slots[i].hash == hash && matches(slots[i].payload) { return slots[i].payload }
            i = (i + 1) & mask
        }
        return nil
    }

    mutating func insert(_ hash: Int, _ payload: Int32) {
        if 2 * (count + 1) > slots.count {
            var bigger = [Slot](repeating: Self.empty, count: 2 * slots.count)
            for s in slots where s.payload >= 0 { Self.place(s, in: &bigger) }
            slots = bigger
        }
        Self.place(Slot(hash: hash, payload: payload), in: &slots)
        count += 1
    }

    private static func place(_ s: Slot, in slots: inout [Slot]) {
        let mask = slots.count - 1
        var i = s.hash & mask
        while slots[i].payload >= 0 { i = (i + 1) & mask }
        slots[i] = s
    }
}

struct ByteSet: Sendable {
    private var store: [UInt8] = []
    private var ranges: [Range<Int>] = []
    private var index = HashIndex()

    static func hash(_ bytes: UnsafeRawBufferPointer) -> Int {
        var h = Hasher()
        h.combine(bytes: bytes)
        return h.finalize()
    }

    func find(_ bytes: UnsafeRawBufferPointer, _ hash: Int) -> Int32? {
        index.find(hash) { store[ranges[Int($0)]].elementsEqual(bytes) }
    }

    mutating func insert(_ bytes: UnsafeRawBufferPointer, _ hash: Int) -> Int32 {
        let id = Int32(ranges.count)
        let start = store.count
        store.append(contentsOf: bytes)
        ranges.append(start..<store.count)
        index.insert(hash, id)
        return id
    }
}
