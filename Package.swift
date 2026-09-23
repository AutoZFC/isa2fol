// swift-tools-version: 6.0
import PackageDescription

// Swift 5 language mode deliberately: this is a single-threaded graph rewriter,
// and 6's strict concurrency would be pure friction here.
let package = Package(
    name: "isa2fol",
    targets: [
        .target(name: "YXML"),
        .target(name: "IR"),
        .target(name: "Lowering", dependencies: ["IR"]),
        .target(name: "FolDialect"),
        .target(name: "Framework", dependencies: ["FolDialect"]),
        .executableTarget(name: "isa2fol", dependencies: ["Framework"]),
        .testTarget(name: "YXMLTests", dependencies: ["YXML"]),
        .testTarget(name: "FolDialectTests", dependencies: ["FolDialect"]),
        .testTarget(name: "IRTests", dependencies: ["IR"]),
        .testTarget(name: "LoweringTests", dependencies: ["Lowering", "IR"]),
    ],
    swiftLanguageModes: [.v5]
)
