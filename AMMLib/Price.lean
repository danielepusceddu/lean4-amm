import AMMLib.Supply
import AMMLib.Swap

noncomputable def Γ.𝕋₁Price_denum
(s: Γ) (m: 𝕋₁)
(h2: 0 < s.mintsupply m): ℝ+ := ⟨s.mintsupply m, h2⟩

noncomputable def Γ.𝕋₁Price_num_addend1
(s: Γ) (c: Cfg)
(m: 𝕋₁) (h1: s.amms.f m.choose m.other ≠ 0)
: ℝ+ := (s.amms.fp h1).fst * (c.o m.choose)

noncomputable def Γ.𝕋₁Price_num_addend2
(s: Γ) (c: Cfg)
(m: 𝕋₁) (h1: s.amms.f m.choose m.other ≠ 0)
: ℝ+ := (s.amms.fp h1).snd * (c.o m.other)

noncomputable def Γ.𝕋₁Price_num
(s: Γ) (c: Cfg)
(m: 𝕋₁) (h1: s.amms.f m.choose m.other ≠ 0)
: ℝ+ :=
(s.𝕋₁Price_num_addend1 c m h1) + (s.𝕋₁Price_num_addend2 c m h1)

noncomputable def Γ.𝕋₁Price 
(s: Γ) (c: Cfg)
(m: 𝕋₁) (h1: s.amms.f m.choose m.other ≠ 0)
(h2: 0 < s.mintsupply m)
: ℝ+ :=
(s.𝕋₁Price_num c m h1) / (s.𝕋₁Price_denum m h2)

@[simp] lemma Swap.𝕋₁Price_denum_diff
{c: Cfg} {s: Γ} (sw: Swap c s) 
(m: 𝕋₁) (h2: 0 < s.mintsupply m)
: sw.apply.𝕋₁Price_denum m ((sw.minted_still_supp h2)) = s.𝕋₁Price_denum m h2
:= by 
unfold Γ.𝕋₁Price_denum
apply Subtype.eq; simp
simp [Swap.mintedSupply]

@[simp] lemma Swap.𝕋₁Price_num_addend1_diff
{c: Cfg} {s: Γ} (sw: Swap c s) 
(m: 𝕋₁) (h1: s.amms.f m.choose m.other ≠ 0)
(hdif: m ≠ 𝕋₀.toMint (AMMSet.exists_imp_dif sw.exi))
: sw.apply.𝕋₁Price_num_addend1 c m (sw.amm_still_exists h1) = s.𝕋₁Price_num_addend1 c m h1
:= by 
unfold Γ.𝕋₁Price_num_addend1
rw [← 𝕋₁.choose_eq m] at hdif
have hdif' := 𝕋₀.toMint_diff hdif
simp [h1, hdif', Swap.amm_fp_diff]

@[simp] lemma Swap.𝕋₁Price_num_addend2_diff
{c: Cfg} {s: Γ} (sw: Swap c s) 
(m: 𝕋₁) (h1: s.amms.f m.choose m.other ≠ 0)
(hdif: m ≠ 𝕋₀.toMint (AMMSet.exists_imp_dif sw.exi))
: sw.apply.𝕋₁Price_num_addend2 c m (sw.amm_still_exists h1) = s.𝕋₁Price_num_addend2 c m h1
:= by 
unfold Γ.𝕋₁Price_num_addend2
rw [← 𝕋₁.choose_eq m] at hdif
have hdif' := 𝕋₀.toMint_diff hdif
simp [h1, hdif', Swap.amm_fp_diff]

@[simp] lemma Swap.𝕋₁Price_num_diff
{c: Cfg} {s: Γ} (sw: Swap c s) 
(m: 𝕋₁) (h1: s.amms.f m.choose m.other ≠ 0)
(hdif: m ≠ 𝕋₀.toMint (AMMSet.exists_imp_dif sw.exi))
: sw.apply.𝕋₁Price_num c m (sw.amm_still_exists h1) = s.𝕋₁Price_num c m h1
:= by 
unfold Γ.𝕋₁Price_num
simp [h1, hdif]

@[simp] theorem Swap.𝕋₁Price_diff 
(c: Cfg) (s: Γ) (sw: Swap c s) 
(m: 𝕋₁) (h1: s.amms.f m.choose m.other ≠ 0)
(h2: 0 < s.mintsupply m)
(hdif: m ≠ 𝕋₀.toMint (AMMSet.exists_imp_dif sw.exi))
: 
(sw.apply.𝕋₁Price c m (sw.amm_still_exists h1) (sw.minted_still_supp h2)) 
=
(s.𝕋₁Price c m h1 h2)
:= by 
unfold Γ.𝕋₁Price
simp [h1, h2, hdif]

noncomputable def Γ.𝕋₁Price_denumz
(s: Γ) (m: 𝕋₁): NNReal := s.mintsupply m

noncomputable def Γ.𝕋₁Price_num_addend1z
(s: Γ) (o: 𝕋₀ → PReal)
(m: 𝕋₁)
: NNReal := (s.amms.f m.choose m.other).fst * (o m.choose)

noncomputable def Γ.𝕋₁Price_num_addend2z
(s: Γ) (o: 𝕋₀ → PReal)
(m: 𝕋₁)
: NNReal := (s.amms.f m.choose m.other).snd * (o m.other)

noncomputable def Γ.𝕋₁Price_numz
(s: Γ) (o: 𝕋₀ → PReal)
(m: 𝕋₁)
: NNReal :=
(s.𝕋₁Price_num_addend1z o m) + (s.𝕋₁Price_num_addend2z o m)

noncomputable def Γ.𝕋₁Pricez
(s: Γ) (o: 𝕋₀ → PReal)
(m: 𝕋₁): NNReal :=
(s.𝕋₁Price_numz o m) / (s.𝕋₁Price_denumz m)