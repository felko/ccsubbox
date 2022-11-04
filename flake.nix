{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;
        coq = pkgs.coq_8_10;
        coq-dpdgraph = (pkgs.coqPackages_8_10.dpdgraph.overrideAttrs (p: p // {
          src = pkgs.fetchFromGitHub {
            owner = "coq-community";
            repo = "coq-dpdgraph";
            rev = "v0.6.6";
            sha256 = "sha256-HDXJcjDz8WzSBLkDIZTWjOijcByr5MajjozwL3+pWb4=";
          };
        }));
      in
      {
        devShell = pkgs.mkShell {
          nativeBuildInputs = with pkgs; [
            coq
            coq-dpdgraph
            (python310.withPackages (pyPkgs: with pyPkgs; [
              fire
              python-lsp-server
            ]))
          ];
        };
      }
    );
}
