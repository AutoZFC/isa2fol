// swift-tools-version: 6.0
import PackageDescription

let package = Package(
    name: "isa2fol",
    targets: [
        .target(name: "YXML"),
        .target(name: "IR"),
        .target(name: "FolDialect", dependencies: ["IR"]),
        .target(name: "Reader", dependencies: ["YXML", "IR"]),
        .target(name: "Lowering", dependencies: ["IR"]),
        .executableTarget(name: "isa2fol", dependencies: ["Reader", "IR", "Lowering", "FolDialect"]),
        .testTarget(name: "YXMLTests", dependencies: ["YXML"]),
        .testTarget(name: "FolDialectTests", dependencies: ["FolDialect", "IR"]),
        .testTarget(name: "IRTests", dependencies: ["IR"]),
        .testTarget(name: "ReaderTests", dependencies: ["Reader", "YXML", "IR"]),
        .testTarget(name: "LoweringTests", dependencies: ["Lowering", "IR", "FolDialect"]),
    ],
    swiftLanguageModes: [.v5],
)
