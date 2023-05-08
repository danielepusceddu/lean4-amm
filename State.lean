import «Tokens»
import «AMMSet»

abbrev State := AccountSet × AMMSet
def State.accs (s: State): AccountSet  := s.1
def State.amms (s: State): AMMSet      := s.2