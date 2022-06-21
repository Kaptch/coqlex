{ pkgs, menhirCoq, mkCoqDerivation, lib }:
{
  package = mkCoqDerivation {
    pname = "coq-menhir";
    version = "${menhirCoq}/coq-menhirlib";
    owner = "Pottier Francois";
    meta = {
      description = "A support library for verified Coq parsers produced by Menhir";
      license = lib.licenses.gpl3Only;
    };
  };
}
