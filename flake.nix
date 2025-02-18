{
  description = "Denotational Semantics";

  inputs = {
    # Nix Inputs
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };

  outputs = {
    self,
    nixpkgs,
  }: let
    forAllSystems = function:
      nixpkgs.lib.genAttrs [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ] (system:
        function rec {
          inherit system;
          pkgs = nixpkgs.legacyPackages.${system};
          agda = pkgs.agda.withPackages (p: [
            p.standard-library
          ]);
        });
  in {
    # nix fmt
    formatter = forAllSystems ({pkgs, ...}: pkgs.alejandra);

    # nix develop
    devShell = forAllSystems ({
      pkgs,
      agda,
      ...
    }:
      pkgs.mkShell {
        shellHook = ''
        '';
        buildInputs = [
          agda
        ];
      });
  };
}
