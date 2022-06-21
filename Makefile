# ********************************************************************#
#                                                                     #
#                 Coqlex verified lexer generator                     #
#                                                                     #
#  Copyright 2021 Siemens Mobility SAS and Institut National de       #
#  Recherche en Informatique et en Automatique.                       #
#  All rights reserved. This file is distributed under                #
#  the terms of the INRIA Non-Commercial License Agreement (see the   #
#  LICENSE file).                                                     #
#                                                                     #
# ********************************************************************#

COQ_SOURCES = UsefullProofs.v MatchLen.v MatchLenSpeedUp.v MatchLenSpeedUp2.v RValues.v SimpleLexerGenerator.v SimpleLexerGeneratorSpeedUp.v SimpleLexerGeneratorSpeedUp2.v Parser.vy Lexer.v

SOURCES = BinNums.mli Datatypes.mli Definitions.mli List0.mli MatchLen.mli MatchLenSpeedUp2.mli Nat.mli Orders.mli OrdersTac.mli PeanoNat.mli Specif.mli String0.mli UsefullProofs.mli BinNums.ml Datatypes.ml Definitions.ml List0.ml MatchLen.ml MatchLenSpeedUp2.ml Nat.ml Orders.ml OrdersTac.ml PeanoNat.ml Specif.ml String0.ml UsefullProofs.ml SimpleLexerGenerator.mli OrdersFacts.mli OrderedType.mli MSetInterface.mli MatchLenSpeedUp.mli FMapList.mli Char0.mli BinPos.mli BinNat.mli BinInt.mli Ascii.mli Alphabet.mli Grammar.mli Int.mli MSetAVL.mli OrdersAlt.mli RValues.mli SimpleLexerGeneratorSpeedUp2.mli SimpleLexerGeneratorSpeedUp.mli BinPos.ml Char0.ml MatchLenSpeedUp.ml OrderedType.ml OrdersAlt.ml OrdersFacts.ml SimpleLexerGenerator.ml SimpleLexerGeneratorSpeedUp2.ml SimpleLexerGeneratorSpeedUp.ml MSetInterface.ml lexerUtils.ml FMapList.ml BinNat.ml BinInt.ml Ascii.ml Alphabet.ml FSetAVL.mli FMapAVL.mli Automaton.mli Interpreter_correct.mli Validator_complete.mli Validator_safe.mli Grammar.ml Int.ml MSetAVL.ml RValues.ml FSetAVL.ml FMapAVL.ml Automaton.ml Interpreter.mli Interpreter_complete.mli Main.mli Parser.mli Interpreter_correct.ml Validator_complete.ml Validator_safe.ml Interpreter.ml Interpreter_complete.ml Lexer.mli Main.ml Parser.ml ParserUtils.ml Lexer.ml coqlex.ml

EXEC = a.out

LIBS=unix.cma -cclib -lunix

all: $(EXEC)

OBJS = $(SOURCES:.ml=.cmo)
OPTOBJS = $(SOURCES2:.ml=.cmx)

COQ_SOURCES1 = $(COQ_SOURCES:.vy=.v)
COQ_OBJS = $(COQ_SOURCES1:.v=.vo)

$(EXEC): $(COQ_OBJS)
	coqc Extraction.v
	ocamlc -c BinNums.mli Datatypes.mli Definitions.mli List0.mli MatchLen.mli MatchLenSpeedUp2.mli Nat.mli Orders.mli OrdersTac.mli PeanoNat.mli Specif.mli String0.mli UsefullProofs.mli BinNums.ml Datatypes.ml Definitions.ml List0.ml MatchLen.ml MatchLenSpeedUp2.ml Nat.ml Orders.ml OrdersTac.ml PeanoNat.ml Specif.ml String0.ml UsefullProofs.ml SimpleLexerGenerator.mli OrdersFacts.mli OrderedType.mli MSetInterface.mli MatchLenSpeedUp.mli FMapList.mli Char0.mli BinPos.mli BinNat.mli BinInt.mli Ascii.mli Alphabet.mli Grammar.mli Int.mli MSetAVL.mli OrdersAlt.mli RValues.mli SimpleLexerGeneratorSpeedUp2.mli SimpleLexerGeneratorSpeedUp.mli BinPos.ml Char0.ml MatchLenSpeedUp.ml OrderedType.ml OrdersAlt.ml OrdersFacts.ml SimpleLexerGenerator.ml SimpleLexerGeneratorSpeedUp2.ml SimpleLexerGeneratorSpeedUp.ml MSetInterface.ml lexerUtils.ml FMapList.ml BinNat.ml BinInt.ml Ascii.ml Alphabet.ml FSetAVL.mli FMapAVL.mli Automaton.mli Interpreter_correct.mli Validator_complete.mli Validator_safe.mli Grammar.ml Int.ml MSetAVL.ml RValues.ml FSetAVL.ml FMapAVL.ml Automaton.ml Interpreter.mli Interpreter_complete.mli Main.mli Parser.mli Interpreter_correct.ml Validator_complete.ml Validator_safe.ml Interpreter.ml Interpreter_complete.ml Lexer.mli Main.ml Parser.ml ParserUtils.ml Lexer.ml coqlex.ml 
	ocamlc -o $(EXEC) $(LIBS) $(OBJS)

.SUFFIXES: .v .vy .vo

.v.vo:
	coqc $<

.vy.v:
	menhir --coq --coq-no-version-check -v $<

coq : $(COQ_OBJS)
	
clean:
	rm -f *.cm[iox] *~ .*~ #*#
	rm -f $(EXEC)
	rm -f $(EXEC).opt
	rm -f *.glob *.vo .*.aux *.crashcoqide Alphabet.ml Alphabet.mli Ascii.ml Ascii.mli Automaton.ml Automaton.mli BinInt.ml BinInt.mli BinNat.ml BinNat.mli BinNums.ml BinNums.mli BinPos.ml BinPos.mli Char0.ml Char0.mli Datatypes.ml Datatypes.mli Definitions.ml Definitions.mli FMapAVL.ml FMapAVL.mli FMapList.ml FMapList.mli FSetAVL.ml FSetAVL.mli Grammar.ml Grammar.mli Interpreter_complete.ml Interpreter_complete.mli Interpreter_correct.ml Interpreter_correct.mli Interpreter.ml Interpreter.mli Int.ml Int.mli Lexer.ml Lexer.mli List0.ml List0.mli Main.ml Main.mli MatchLen.ml MatchLen.mli MatchLenSpeedUp.ml MatchLenSpeedUp.mli MatchLenSpeedUp2.ml MatchLenSpeedUp2.mli MSetAVL.ml MSetAVL.mli MSetInterface.ml MSetInterface.mli Nat.ml Nat.mli OrderedType.ml OrderedType.mli OrdersAlt.ml OrdersAlt.mli OrdersFacts.ml OrdersFacts.mli Orders.ml Orders.mli OrdersTac.ml OrdersTac.mli Parser.ml Parser.mli PeanoNat.ml PeanoNat.mli RValues.ml RValues.mli SimpleLexerGenerator.ml SimpleLexerGenerator.mli SimpleLexerGeneratorSpeedUp.ml SimpleLexerGeneratorSpeedUp.mli SimpleLexerGeneratorSpeedUp2.ml SimpleLexerGeneratorSpeedUp2.mli Specif.ml Specif.mli String0.ml String0.mli UsefullProofs.ml UsefullProofs.mli Validator_complete.ml Validator_complete.mli Validator_safe.ml Validator_safe.mli *.o Parser.automaton Parser.conflicts Parser.v

