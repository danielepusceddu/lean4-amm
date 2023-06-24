import AMMLib.Wallets
import AMMLib.State
import AMMLib.Price

def atomicworth 
(o: 𝕋₀ → PReal) (t: 𝕋₀) (x: NNReal)
: NNReal := (o t)*x

noncomputable def 𝕎₀.networth
(w: 𝕎₀) (o: 𝕋₀ → PReal): NNReal :=
w.sum (atomicworth o)

theorem atomicworth_zero (o: 𝕋₀ → PReal)
: ∀ (t: 𝕋₀), (atomicworth o) t 0 = 0 := by
intro t; simp [atomicworth]

theorem 𝕎₀.networth_destruct
(w: 𝕎₀) (o: 𝕋₀ → PReal)
(t: 𝕋₀)
: (𝕎₀.networth w o) = (o t)*(w t) + (𝕎₀.networth (Finsupp.erase t w) o) := by 
unfold networth
rw [← Finsupp.add_sum_erase' w t (atomicworth o) (atomicworth_zero o)]
simp [atomicworth]

noncomputable def mintedworth
(s: Γ) (o: 𝕋₀ → PReal) (t: 𝕋₁) (x: NNReal)
: NNReal := (s.𝕋₁Pricez o t)*x

theorem mintedworth_zero 
(s: Γ) (o: 𝕋₀ → PReal)
: ∀ (t: 𝕋₁), (mintedworth s o) t 0 = 0 := by
intro t; simp [mintedworth]

noncomputable def 𝕎₁.networth
(w: 𝕎₁) (s: Γ) (o: 𝕋₀ → PReal): NNReal :=
w.sum (mintedworth s o)

theorem 𝕎₁.networth_destruct
(w: 𝕎₁) (s: Γ) (o: 𝕋₀ → PReal)
(t: 𝕋₁)
: (𝕎₁.networth w s o) = (s.𝕋₁Pricez o t)*(w t) + (𝕎₁.networth (Finsupp.erase t w) s o) := by 
unfold networth
rw [← Finsupp.add_sum_erase' w t (mintedworth s o) (mintedworth_zero s o)]
simp [mintedworth]

noncomputable def Γ.networth
(s: Γ) (a: 𝔸) (o: 𝕋₀ → PReal): NNReal
:=
(𝕎₀.networth (s.atoms a) o)
+
(𝕎₁.networth (s.mints a) s o)

noncomputable def 𝔸.gain
(a: 𝔸) (o: 𝕋₀ → PReal) (s s': Γ)
: ℝ
:= ((s'.networth a o): ℝ) - ((s.networth a o): ℝ)
