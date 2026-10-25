{
  description = "Rota's umbral calculus as a polymorphic language with dictionary passing";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";

  outputs =
    { self, nixpkgs }:
    let
      # Nix provides the toolchain only. Haskell libraries are resolved by
      # cabal against Hackage, not packaged here.
      ghcName = "ghc9103";

      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          name = "umbral";

          packages = [
            # Bare compiler: its package db holds boot libraries only.
            pkgs.haskell.compiler.${ghcName}

            # HLS must be built against the same GHC or it cannot load the project.
            pkgs.haskell.packages.${ghcName}.haskell-language-server

            # Standalone executables, so the GHC they were built with is irrelevant.
            pkgs.cabal-install
            pkgs.ghcid
            pkgs.hlint
            pkgs.ormolu
            pkgs.nixfmt-rfc-style

            # For Hackage packages that want C libraries at build time.
            pkgs.pkg-config
            pkgs.zlib
          ];
        };
      });

      formatter = forAllSystems (pkgs: pkgs.nixfmt-rfc-style);
    };
}
