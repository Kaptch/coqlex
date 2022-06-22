{
  description = "Coqlex flake";
  
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/master";
    flake-utils.url = "github:numtide/flake-utils";
    regexp = {
      url = "https://github.com/Kaptch/regexp.git";
      ref = "master";
      type = "git";
      flake = false;
    };
    menhirCoq = {
      url = "https://gitlab.inria.fr/fpottier/menhir.git";
      ref = "master";
      type = "git";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, regexp, menhirCoq }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let pkgs = nixpkgs.legacyPackages.${system};
            mkCoqDerivation = pkgs.coqPackages_8_15.mkCoqDerivation;
            lib = nixpkgs.lib;
        in
        {
          devShell = pkgs.mkShell {
            buildInputs =
              let coq-regexp = import ./regexp-coq.nix { inherit pkgs regexp mkCoqDerivation lib; };
                  coq-menhir = import ./menhir-coq.nix { inherit pkgs menhirCoq mkCoqDerivation lib; };
              in
                [
                  pkgs.coq_8_15
                  pkgs.gnumake
                  pkgs.ocaml
                  coq-menhir.package
                  coq-regexp.package
                  pkgs.ocamlPackages.menhir
                  pkgs.ocamlPackages.stdlib-shims
                ];
          };
          # apps.default = { type = "app";
          #                  program = "${self.packages.${system}."coq8.15-coq-coqlex-dev"}/bin/coqlex";
          #                };
          packages.default = mkCoqDerivation {
            pname = "coq-coqlex";
            version = "./";
            src = ./.;
            buildPhase = "make";
            installPhase = ''
  mkdir -p $out/bin
  cp ./a.out $out/bin/coq-coqlex
  '';
            owner = "Wendlasida OUEDRAOGO & Danko ILIK & Lutz STRASSBURGER";
            meta = {
              description = "These source files contain the implementation, models, and proof of correctness of a formally verified lexers. A verified lexer (or RecLexer) is a lexer that satisfies correctness properties about positions and character consumption. We implemented a constructor for RecLexer from a specification : a list of regular expressions and actions.";
              license = {
                fullName  = "Inria Non-Commercial License Agreement for the Coqlex verified lexer generator";
                free      = true;
              };
            };
            propagatedBuildInputs =
              [
                (import ./regexp-coq.nix { inherit pkgs regexp mkCoqDerivation lib; }).package
                (import ./menhir-coq.nix { inherit pkgs menhirCoq mkCoqDerivation lib; }).package
                pkgs.ocamlPackages.menhir
                pkgs.ocaml
                pkgs.ocamlPackages.stdlib-shims
              ];
          };
        }
      );
}
