{ pkgs, regexp, mkCoqDerivation, lib }:
{
  package = mkCoqDerivation {
    pname = "coq-regexp";
    version = "${regexp}";
    owner = "Takashi Miyamoto";
    meta = {
      description = ''The Library RegExp is a Coq library for regular expression. The implementation is based on the Janusz Brzozowski's algorithm ("Derivatives of Regular Expressions", Journal of the ACM 1964).
The RegExp library satisfies the axioms of Kleene Algebra.  The proofs are shown in the library.'';
      license = lib.licenses.lgpl2Only;
    };
  };
}
