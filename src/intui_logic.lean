import heyting
import tactic.induction

open heyting

namespace intuitionistic_logic

universe u

inductive prop_formula
| bot : prop_formula
| var : ℕ → prop_formula
| imp : prop_formula → prop_formula → prop_formula
| or : prop_formula → prop_formula → prop_formula
| and : prop_formula → prop_formula → prop_formula

notation ⊥ := prop_formula.bot
notation ¬ := λp : prop_formula, p.imp ⊥
infixr ` \/ `:5 := prop_formula.or
infixr ` /\ `:5 := prop_formula.and

instance : has_imp prop_formula := ⟨prop_formula.imp⟩

inductive intui_thm : set prop_formula → prop_formula → Prop
| ax : ∀{Γ p}, p ∈ Γ → intui_thm Γ p
| imp_i : ∀{Γ p q}, intui_thm (Γ ∪ {p}) q → intui_thm Γ (p => q)
| imp_e : ∀{Γ p q}, intui_thm Γ (p => q) → intui_thm Γ p → intui_thm Γ q
| or_il : ∀{Γ p} q, intui_thm Γ p → intui_thm Γ (p \/ q)
| or_ir : ∀{Γ q} p, intui_thm Γ q → intui_thm Γ (p \/ q)
| or_e : ∀{Γ p q r}, intui_thm Γ (p \/ q) → intui_thm (Γ ∪ {p}) r → 
intui_thm (Γ ∪ {q}) r → intui_thm Γ r
| and_i : ∀{Γ p q}, intui_thm Γ p → intui_thm Γ q → intui_thm Γ (p /\ q)
| and_el : ∀{Γ p q}, intui_thm Γ (p /\ q) → intui_thm Γ p
| and_er : ∀{Γ p q}, intui_thm Γ (p /\ q) → intui_thm Γ q
| bot_e : ∀{Γ p}, intui_thm Γ ⊥ → intui_thm Γ p

infix ` ⊢ `:50 := intui_thm

variables {Γ : set prop_formula} {p q r : prop_formula}

lemma proves_of_subset_proves {Γ' : set prop_formula} : Γ' ⊆ Γ → Γ' ⊢ p → Γ ⊢ p :=
begin 
	intros hss hGp,
	induction hGp generalizing Γ,
	{ exact intui_thm.ax (hss hGp_ᾰ) },
	{
		apply intui_thm.imp_i,
		have : hGp_Γ ∪ {hGp_p} ⊆ Γ ∪ {hGp_p},
		{
			intros x hx,
			simp at *,
			cases hx,
			{exact or.inl hx},
			{exact or.inr (hss hx)},
		},
		exact hGp_ih this,
	},
	{ exact intui_thm.imp_e (hGp_ih_ᾰ hss) (hGp_ih_ᾰ_1 hss) },
	{ exact intui_thm.or_il hGp_q (hGp_ih hss) },
	{ exact intui_thm.or_ir hGp_p (hGp_ih hss) },
	{
		apply intui_thm.or_e (hGp_ih_ᾰ hss),
		{ exact hGp_ih_ᾰ_1  (set.union_subset_union_left {hGp_p} hss) },
		{ exact hGp_ih_ᾰ_2 (set.union_subset_union_left {hGp_q} hss) },
	},
	{ exact intui_thm.and_i (hGp_ih_ᾰ hss) (hGp_ih_ᾰ_1 hss) },
	{ exact intui_thm.and_el (hGp_ih hss) },
	{ exact intui_thm.and_er (hGp_ih hss) },
	{ exact intui_thm.bot_e (hGp_ih hss) }
end

theorem deduction_thm : Γ ∪ {p} ⊢ q ↔ Γ ⊢ (p => q) :=
begin 
	split,
	{ exact λh, intui_thm.imp_i h },
	{
		intro h,
		have h1 := proves_of_subset_proves (set.subset_union_left Γ {p}) h,
		have h2 : Γ ∪ {p} ⊢ p,
		{
			apply intui_thm.ax,
			finish,
		},
		exact intui_thm.imp_e h1 h2,
	},
end

lemma fin_subset_proves_of_proves {Γ : set prop_formula} {φ : prop_formula}
  (h : Γ ⊢ φ) : ∃ (Δ : set prop_formula), Δ ⊆ Γ ∧ Δ.finite ∧ Δ ⊢ φ :=
begin
	sorry; {
	induction' h,
	{
		use [{φ}, by rwa set.singleton_subset_iff, set.finite_singleton _],
		apply intui_thm.ax, apply set.mem_singleton,
	},
	{
		rcases ih with ⟨Δ, h1, h2, h3⟩,
		use [Δ \ {φ}, by rwa [set.diff_subset_iff, set.union_comm], set.finite.diff h2 _],
		apply intui_thm.imp_i,
		rw set.diff_union_self,
		exact proves_of_subset_proves (set.subset_union_left Δ {φ}) h3,
	},
	{
		rcases ih_h with ⟨Δ, h1, h2, h3⟩,
		rcases ih_h_1 with ⟨Δ', h1', h2', h3'⟩,
		use [Δ ∪ Δ', set.union_subset h1 h1', set.finite.union h2 h2'],

		have t1 := proves_of_subset_proves (set.subset_union_left Δ Δ') h3,
		have t2 := proves_of_subset_proves (set.subset_union_right Δ Δ') h3',

		exact intui_thm.imp_e t1 t2,
	},
	{
		rcases ih with ⟨Δ, h1, h2, h3⟩,
		use [Δ, h1, h2, intui_thm.or_il φ_1 h3],
	},
	{
		rcases ih with ⟨Δ, h1, h2, h3⟩,
		use [Δ, h1, h2, intui_thm.or_ir φ_1 h3],
	},
	{
		rcases ih_h with ⟨Δ1, h1_1, h1_2, h1_3⟩,
		rcases ih_h_1 with ⟨Δ2, h2_1, h2_2, h2_3⟩,
		rcases ih_h_2 with ⟨Δ3, h3_1, h3_2, h3_3⟩,
		use [Δ1 ∪ (Δ2 \ {p}) ∪ Δ3 \ {q}], split,
		{
			intros x hx,
			cases hx, cases hx,
			{ exact h1_1 hx },
			{
				have h1 : Δ2 \ {p} ⊆ Δ2 := set.diff_subset Δ2 {p},
				have h2 := h1 hx,
				have x_ne_p : x ≠ p := by finish,
				cases h2_1 h2,
				{ exact h_3 },
				{ finish },
			},
			{
				have h1 : Δ3 \ {q} ⊆ Δ3 := set.diff_subset Δ3 {q},
				have h2 := h1 hx,
				have x_ne_p : x ≠ q := by finish,
				cases h3_1 h2,
				{ exact h_3 },
				{ finish },
			},
		},
		split,
		{
			apply set.finite.union,
			{
				apply set.finite.union,
				{ exact h1_2 },
				{ exact set.finite.diff h2_2 {p}}
			},
			{ exact set.finite.diff h3_2 _},
		}, 
		rw set.union_assoc,
		apply intui_thm.or_e 
		(proves_of_subset_proves (set.subset_union_left Δ1 (Δ2 \ {p} ∪ Δ3 \ {q})) h1_3),
		have h1 : Δ2 ⊆ Δ1 ∪ (Δ2 \ {p} ∪ Δ3 \ {q}) ∪ {p},
		{
			intros x hx,
			by_cases hxp : x = p;finish,
		},
		exact proves_of_subset_proves h1 h2_3,

		have h2 : Δ3 ⊆ Δ1 ∪ (Δ2 \ {p} ∪ Δ3 \ {q}) ∪ {q},
		{
			intros x hx,
			by_cases hxp : x = p;finish,
		},
		exact proves_of_subset_proves h2 h3_3,
	},
	{
		rcases ih_h with ⟨Δ1, h1_1, h1_2, h1_3⟩,
		rcases ih_h_1 with ⟨Δ2, h2_1, h2_2, h2_3⟩,
		use [Δ1 ∪ Δ2, set.union_subset h1_1 h2_1, set.finite.union h1_2 h2_2,
		 (proves_of_subset_proves (set.subset_union_left Δ1 Δ2) h1_3).and_i
  	(proves_of_subset_proves (set.subset_union_right Δ1 Δ2) h2_3)],
	},
	{
		rcases ih with ⟨Δ, h1, h2, h3⟩,
		use [Δ, h1, h2, intui_thm.and_el h3],
	},
	{
		rcases ih with ⟨Δ, h1, h2, h3⟩,
		use [Δ, h1, h2, intui_thm.and_er h3],
	},
	{
		rcases ih with ⟨Δ, h1, h2, h3⟩,
		use [Δ, h1, h2, intui_thm.bot_e h3],
	}
	}
end

variables {H : Type u} [heyting H]

def assignment (H : Type u) [heyting H] := ℕ → H
def value (s : assignment H) : prop_formula → H 
| ⊥ := ⊥
| (prop_formula.var n) := s n
| (p \/ q) := value p ∪ value q 
| (p /\ q) := (value p) ∩ value q
| (prop_formula.imp p q) := value p => value q

def intui_implies (H : Type u) [heyting H] {Γ : set prop_formula} (Γ_fin : set.finite Γ) (p : prop_formula) :=
∀ (s : assignment H), infimum_of_finite (set.finite.image (value s) Γ_fin) ≤ value s p

lemma pseudo_soundness (H : Type u) [heyting H] (Γ_fin : set.finite Γ) :
 Γ ⊢ p → (intui_implies H Γ_fin p) :=
begin 
	intro Γ_proves,
	induction' Γ_proves,
	{
		intro s,
		have : (@value H _inst_2 s) p ∈ (@value H _inst_2 s ) '' Γ := 
		set.mem_image_of_mem _ h,
		have h_inf := @infimum_of_finite_spec H _inst_2 ((@value H _inst_2 s ) '' Γ) 
		(set.finite.image (@value H _inst_2 s) Γ_fin),
		exact h_inf.1 this,
	},
	{
		intros s,
		have ih2 := @ih H _inst_2 (by finish) s,
	}
end


end intuitionistic_logic