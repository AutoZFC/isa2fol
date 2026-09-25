// swift-tools-version: 6.0
import PackageDescription

// Swift 5 language mode deliberately: this is a single-threaded graph rewriter,
// and 6's strict concurrency would be pure friction here.
let package = Package(
    name: "isa2fol",
    targets: [
        .target(name: "YXML"),
        .target(name: "IR"),
        .target(name: "FolDialect", dependencies: ["IR"]),
        .target(name: "Reader", dependencies: ["YXML", "IR"]),
        .executableTarget(name: "isa2fol"),
        .testTarget(name: "YXMLTests", dependencies: ["YXML"]),
        .testTarget(name: "FolDialectTests", dependencies: ["FolDialect", "IR"]),
        .testTarget(name: "IRTests", dependencies: ["IR"]),
        .testTarget(name: "ReaderTests", dependencies: ["Reader", "YXML", "IR"]),
    ],
    swiftLanguageModes: [.v5]
)
