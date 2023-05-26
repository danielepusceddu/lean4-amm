import AMMLib.Tokens
import AMMLib.AMMSet

-- Config does not change between states.
-- This is where I would add φ.
-- The price oracle should be moved to 
-- State to implement price updates.
structure Config where
  sx: PReal → (PReal × PReal) → PReal
  o: AtomicTok → PReal

structure State where
  atoms: AtomicWalls
  mints: MintedWalls
  amms: AMMSet

def joinWall (a: AtomicTok →₀ NNReal) (m: MintedTok →₀ NNReal)
: Token →₀ NNReal := 
⟨ 
  (Finset.map Token.Atomic_emb a.support)
  ∪
  (Finset.map Token.Minted_emb m.support),
  (λ (t: Token) => (
    match t with
    | Token.Atomic t' => a t'
    | Token.Minted t' => m t')),

  (by intro t
      apply Iff.intro
      . intro incup
        simp at incup
        simp
        rcases incup with ⟨atom,⟨nonzero,isatom⟩⟩|⟨mint,⟨nonzero,ismint⟩⟩
        . simp [Token.Atomic_emb] at isatom
          simp [← isatom]
          exact nonzero
        . simp [Token.Minted_emb] at ismint
          simp [← ismint]
          exact nonzero
        
      . cases t with
        | Atomic t' => 
          simp; intro nonzero
          left; exists t'; 
        | Minted t' =>
          simp; intro nonzero
          right; exists t';)
⟩  

def State.accs (s: State): TokenWalls := 
⟨ 
  s.atoms.support ∪ s.mints.support,
  λ (a: Account) => joinWall (s.atoms a) (s.mints a),
  by intro a
     apply Iff.intro
     . intro incup
       simp
       simp at incup
       apply Finsupp.nonzero_iff_exists.mpr
       rcases incup with left|right
       . have ⟨witness, prop⟩ := (Finsupp.nonzero_iff_exists).mp left
         exists witness
       . have ⟨witness, prop⟩ := (Finsupp.nonzero_iff_exists).mp right
         exists witness
     . intro nonzero
       simp at nonzero
       simp
       have nonzero' := (Finsupp.nonzero_iff_exists).mp nonzero
       have ⟨witness, prop⟩ := nonzero'
       cases witness with
       | Atomic t' => 
          simp [joinWall] at prop
          left; apply (Finsupp.nonzero_iff_exists).mpr
          exists t'
       | Minted t' =>
          simp [joinWall] at prop
          right; apply (Finsupp.nonzero_iff_exists).mpr
          exists t'
⟩
