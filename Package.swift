// swift-tools-version: 6.0
import PackageDescription

// Swift 5 language mode deliberately: this is a single-threaded tree walker,
// and 6's strict concurrency would be pure friction here.
let package = Package(
    name: "isa2fol",
    targets: [
        .target(name: "YXML"),
        .target(name: "IR"),
        .target(name: "IsaDialect", dependencies: ["YXML"]),
        .target(name: "FolDialect"),
        .target(name: "Framework", dependencies: ["IsaDialect", "FolDialect"]),
        .executableTarget(name: "isa2fol", dependencies: ["Framework"]),
        .testTarget(name: "YXMLTests", dependencies: ["YXML"]),
        .testTarget(name: "IsaDialectTests", dependencies: ["IsaDialect"]),
        .testTarget(name: "FolDialectTests", dependencies: ["FolDialect"]),
        .testTarget(name: "IRTests", dependencies: ["IR"]),
    ],
    swiftLanguageModes: [.v5]
)
