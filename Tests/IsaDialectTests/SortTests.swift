import Testing
@testable import IsaDialect

@Test func groundnessIsStructural() {
    #expect(Sort.i.isGround)
    #expect(Sort.arrow(.i, .o).isGround)
    #expect(!Sort.variable("'a").isGround)
    #expect(!Sort.arrow(.i, .variable("'a")).isGround,
            "a type variable anywhere makes the whole sort non-ground")
}
