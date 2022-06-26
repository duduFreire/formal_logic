import tactic 
import tactic.induction
import order.zorn


namespace prop_logic

inductive prop_formula
| bot : prop_formula
| var : ℕ → prop_formula
| imp : prop_formula → prop_formula → prop_formula

notation ⊥ := prop_formula.bot
notation ¬ := λp : prop_formula, p.imp ⊥
infixr ` ->> `:5 := prop_formula.imp

inductive prop_thm : set prop_formula → prop_formula → Prop 
| ax : ∀{Γ p}, p ∈ Γ → prop_thm Γ p
| imp_i : ∀{Γ p q}, prop_thm (Γ ∪ {p}) q → prop_thm Γ (p ->> q)
| imp_e : ∀{Γ p q}, prop_thm Γ (p ->> q) → prop_thm Γ p → prop_thm Γ q
| bot_e : ∀{Γ p}, prop_thm Γ ⊥ → prop_thm Γ p
| lem : ∀{Γ p q}, prop_thm Γ ((¬q) ->> (¬p)) → prop_thm Γ (p ->> q)

infix ` ⊢ `:50 := prop_thm

notation `assignment` := ℕ → Prop

def value (s : assignment) : prop_formula → Prop
| ⊥ := false
| (prop_formula.var n) := s n
| (p ->> q) := value p → value q

def satisfies (s : assignment) (Γ : set prop_formula) : Prop
 := ∀{p}, p ∈ Γ → value s p
def satisfiable (Γ : set prop_formula) : Prop := ∃s, satisfies s Γ
def tautology (p : prop_formula) : Prop := ∀ s : assignment, value s p
def contradiction (p : prop_formula) : Prop := ∀ s : assignment, ¬(value s p)
def logically_implies (Γ : set prop_formula) (p : prop_formula) : Prop :=
∀{s}, satisfies s Γ → value s p
def inconsistent (Γ : set prop_formula) := Γ ⊢ ⊥
def consistent (Γ : set prop_formula) := ¬(Γ ⊢ ⊥)

infix ` ⊨ `: 5 := logically_implies

lemma proves_of_proves_bot {Γ φ} : (Γ ⊢ ⊥) → (Γ ⊢ φ) :=
λh, prop_thm.bot_e h

lemma inconsistent_iff_proves_all (Γ : set prop_formula) :
inconsistent Γ ↔ ∀p, Γ ⊢ p := 
⟨
	λh p, prop_thm.bot_e h, 
	λh, h ⊥
⟩

lemma inconsistent_iff_proves_contra (Γ : set prop_formula) :
inconsistent Γ ↔ (Γ ⊢ ((prop_formula.var 0 ->> prop_formula.var 0) ->> ⊥)) :=
begin
	split,
	{
		intro h,
		exact (inconsistent_iff_proves_all Γ).mp h 
		((prop_formula.var 0 ->> prop_formula.var 0) ->> ⊥),
	},
	{
		intro h,
		apply prop_thm.imp_e h,
		apply prop_thm.imp_i,
		apply prop_thm.ax,
		simp,
	},
end

lemma proves_of_subset_proves {Γ Δ : set prop_formula} {p : prop_formula} :
 Δ ⊆ Γ → (Δ ⊢ p) → (Γ ⊢ p) :=
begin
	intros hss hDp,
	induction hDp with a b c d e f g h i j k l m n o p q r s t u v w x generalizing Γ,
	{
		apply prop_thm.ax,
		exact hss c,
	},
	{
		apply prop_thm.imp_i,
		have : d ∪ {e} ⊆ Γ ∪ {e},
		{
			intros x hx,
			simp at *,
			cases hx,
			{exact or.inl hx},
			{exact or.inr (hss hx)},
		},
		exact h this,
	},
	{
		specialize n hss,
		specialize o hss,
		exact prop_thm.imp_e n o,
	},
	{
		specialize s hss,
		exact prop_thm.bot_e s,
	},
	{
		specialize x hss,
		exact prop_thm.lem x,
	}
end

lemma proves_of_empty_proves (Γ : set prop_formula) {p : prop_formula} :
∅ ⊢ p → Γ ⊢ p := λh, proves_of_subset_proves (set.empty_subset Γ) h

lemma valid_imp_of_neg_premise (p q : prop_formula) : ∅ ⊢ ((¬p) ->> (p ->> q)) :=
begin
	apply prop_thm.imp_i,
	apply prop_thm.imp_i,
	apply prop_thm.bot_e,
	simp,
	have t1 := prop_thm.ax (set.mem_insert p {p ->> ⊥}),
	have t2 : {p, p ->> ⊥} ⊢ (p ->> ⊥) := prop_thm.ax (by simp at *),
	exact prop_thm.imp_e t2 t1,
end

theorem deduction_thm (Γ : set prop_formula) (p q : prop_formula) :
(Γ ∪ {p} ⊢ q) ↔ (Γ ⊢ (p ->> q)) :=
begin
	split,
	{
		intro h,
		apply prop_thm.imp_i,
		exact h,
	},
	{
		intro h,
		have := proves_of_subset_proves (set.subset_union_left Γ {p}) h,
		exact prop_thm.imp_e this 
		(begin
		apply prop_thm.ax,
		simp,
		end),
	},
end

theorem soundness {Γ φ} : (Γ ⊢ φ) → (Γ ⊨ φ) :=
begin
	intros hΓφ s hΓs,
	induction hΓφ with a b c d e f g h i j k l m n o p q r s t u v w x,
	{
		exact hΓs c,
	},
	{
		intro h1,
		apply h,
		intros x hx,
		simp at hx,
		cases hx,
		{rwa hx},
		{exact hΓs hx},
	},
	{
		specialize n @hΓs,
		specialize o @hΓs,
		exact n o,
	},
	{
		exfalso,
		exact (s @hΓs),
	},
	{
		intro h,
		specialize x @hΓs,
		unfold value at *,
		tauto!,
	}
end

lemma consistent_of_satisfiable {Γ} : satisfiable Γ → consistent Γ :=
begin
	intro h,
	cases h with s hs,
	apply mt (@soundness Γ ⊥),
	intro contra,
	exact contra (by assumption),
end

lemma empty_consistent : consistent ∅ :=
begin
	apply consistent_of_satisfiable,
	use (λn, true),
	intros x hx, exfalso,
	exact set.not_mem_empty _ hx,
end

lemma consistent_of_not_proves {Γ : set prop_formula} {φ : prop_formula} :
¬(Γ ⊢ φ) → (consistent (Γ ∪ {¬φ})) :=
begin
	unfold consistent, contrapose, push_neg,
	intro h,
	change inconsistent (Γ ∪ {φ ->> ⊥}) at h,
	rw inconsistent_iff_proves_contra at h,
	rw deduction_thm at h,

	apply prop_thm.imp_e (prop_thm.lem h),
	apply prop_thm.imp_i,
	apply prop_thm.ax,
	simp,
end

lemma consistent_of_proves {Γ : set prop_formula} {φ : prop_formula} :
 (Γ ⊢ φ) → consistent Γ → (consistent (Γ ∪ {φ})) :=
begin
	intro h,
	contrapose,
	intro h1,
	unfold consistent at *, push_neg at h1 ⊢,
	have := prop_thm.imp_i h1,
	exact prop_thm.imp_e this h,
end


lemma completeness_iff : 
(∀{Γ φ}, (Γ ⊨ φ) → (Γ ⊢ φ)) ↔ (∀{Γ}, consistent Γ → satisfiable Γ) :=
begin
	split,
	{
		intros h Γ hΓ,
		specialize @h Γ ⊥,
		have h1 : ¬(Γ ⊢ ⊥) → ¬(Γ ⊨ ⊥) := mt h, clear h,
		specialize h1 hΓ,
		unfold logically_implies at h1,
		push_neg at h1,
		cases h1 with s hs,
		exact ⟨s, hs.1⟩,
	},
	{
		intros h Γ φ,
		contrapose,
		intros hΓφ contra,
		have := consistent_of_not_proves hΓφ,
		specialize h this,
		cases h with s hs, dsimp only at hs,
		have hsΓ : satisfies s Γ := λx hx, hs (set.mem_union_left {φ ->> ⊥} hx),
		have hsΓnφ : value s (φ ->> ⊥) := hs (by simp),
		apply hsΓnφ,
		exact contra (by assumption),
	}
end

def maximal_consistent (Γ : set prop_formula) := consistent Γ ∧ ∀p, p ∉ Γ → (¬p) ∈ Γ

lemma mem_maximal_consistent_iff_proves {Γ : set prop_formula} :
maximal_consistent Γ → ∀p, (p ∈ Γ ↔ Γ ⊢ p) := 
begin
	intros hΓ p,
	split,
	{exact λh, prop_thm.ax h},
	{
		contrapose,
		intros h contra,
		have t1 := hΓ.2 p h, dsimp only at t1,
		have := prop_thm.imp_e (prop_thm.ax t1) contra,
		exact hΓ.1 this,
	}
end

lemma maximal_consistent_iff (Γ : set prop_formula) : maximal_consistent Γ ↔ (consistent Γ ∧ 
∀Δ, consistent Δ → ¬ (Γ ⊂ Δ)) := 
begin
	split,
	{
		intros h,
		split,
		{exact h.1},
		intros Δ hΔ contra,
		rw ssubset_iff_subset_not_subset at contra,
		have : ∃φ, φ ∈ Δ ∧ φ ∉ Γ,
		{
			by_contra h1,
			push_neg at h1,
			exact contra.2 h1,
		},
		cases this with φ hφ,
		have := contra.1 (h.2 _ hφ.2), dsimp only at this,
		exact hΔ (prop_thm.imp_e (prop_thm.ax this) (prop_thm.ax hφ.1)),
	},
	{
		intros h, use h.1,
		intros p hp, dsimp only,
		cases h with Γ_con h,
		have mem_Γ : ∀{p}, Γ ⊢ p ↔ (p ∈ Γ),
		{
			intros q,
			split,
			{
				intro h1, by_contra hq,
				have := h _ (consistent_of_proves h1 Γ_con),
				apply this,
				rw ssubset_iff_subset_not_subset,
				use set.subset_union_left Γ {q},
				intro contra,
				have : q ∈ Γ,
				{
					apply contra,
					simp at *,
				},
				exact hq this,
			},
			{
				intro h,
				exact prop_thm.ax h,
			},
		},
		rw← mem_Γ at hp,
		have temp := h _ (consistent_of_not_proves hp), dsimp only at temp,
		by_contra contra,
		apply temp,
		split, {exact set.subset_union_left Γ {p ->> ⊥}},
		intros h1,
		exact contra (h1 (by simp at *)),
	},
end

lemma satisfiable_of_maximal_consistent {Γ : set prop_formula} :
 maximal_consistent Γ → satisfiable Γ :=
begin
	intro h,
	set s := λn : ℕ, @ite Prop ((prop_formula.var n) ∈ Γ) 
	(classical.dec (prop_formula.var n ∈ Γ)) true false with s_def,

	have s_pos : ∀n, (prop_formula.var n ∈ Γ) → s n = true,
	{
		intros n hn,
		finish,
	},
	have s_neg : ∀n, (prop_formula.var n ∉ Γ) → s n = false,
	{
		intros n hn,
		finish,
	},
	have s_iff : ∀n, s n ↔ (prop_formula.var n) ∈ Γ,
	{
		intro n,
		split,
		{
			intro h1,
			by_contra,
			specialize s_neg n h,
			rw← s_neg,
			exact h1,
		},
		{
			intro h1,
			specialize s_pos n h1,
			rw s_pos,
			trivial,
		},
	},

	have : ∀p, value s p ↔ p ∈ Γ,
	{
		intro p,
		induction p with a b c d e f g h i j k l m n o p q r s t u v w x,
		{exact ⟨by tauto, λh1, h.left (prop_thm.ax h1)⟩},
		{
			rw← s_iff,
			refl,
		},
		{
			split,
			{
				intro h1,
				unfold value at h1,
				by_contra h2,
				have hbc := h.2 (b ->> c) h2,
				rw [d, e] at h1,
				by_cases h3 : b ∈ Γ,
				{
					have h4 := h1 h3,
					have temp1 : Γ ⊢ (b ->> c),
					{
						apply prop_thm.imp_i,
						have obv : Γ ⊆ Γ ∪ {b} := set.subset_union_left Γ {b},
						exact proves_of_subset_proves obv (prop_thm.ax h4),
					},
					apply h.1,
					apply prop_thm.imp_e (prop_thm.ax hbc),
					exact temp1,
				},
				have hnb := h.2 b h3, dsimp only at hnb,
				have t1 := proves_of_empty_proves Γ (valid_imp_of_neg_premise b c),
				simp at t1,
				have t2 := prop_thm.imp_e t1 (prop_thm.ax hnb),
				simp at hbc,
				exact h.1 (prop_thm.imp_e (prop_thm.ax hbc) t2),
			},
			{
				intros h1 hb,
				rw d at *,
				rw e,
				rw mem_maximal_consistent_iff_proves h at *,
				exact prop_thm.imp_e h1 hb,
			},
		},
	},

	use s,
	intros p hp,
	rwa← this p at hp,
end

lemma fin_subset_proves_of_proves {Γ : set prop_formula} {φ : prop_formula}
  (h : Γ ⊢ φ) : ∃ (Δ : set prop_formula), Δ ⊆ Γ ∧ Δ.finite ∧ Δ ⊢ φ :=
begin
	induction' h,
	{
		use [{φ}, by rwa set.singleton_subset_iff, set.finite_singleton _],
		apply prop_thm.ax, apply set.mem_singleton,
	},
	{
		rcases ih with ⟨Δ, h1, h2, h3⟩,
		use [Δ \ {φ}, by rwa [set.diff_subset_iff, set.union_comm], set.finite.diff h2 _],
		apply prop_thm.imp_i,
		rw set.diff_union_self,
		exact proves_of_subset_proves (set.subset_union_left Δ {φ}) h3,
	},
	{
		rcases ih_h with ⟨Δ, h1, h2, h3⟩,
		rcases ih_h_1 with ⟨Δ', h1', h2', h3'⟩,
		use [Δ ∪ Δ', set.union_subset h1 h1', set.finite.union h2 h2'],

		have t1 := proves_of_subset_proves (set.subset_union_left Δ Δ') h3,
		have t2 := proves_of_subset_proves (set.subset_union_right Δ Δ') h3',

		exact prop_thm.imp_e t1 t2,
	},
	{
		rcases ih with ⟨Δ, h1, h2, h3⟩,
		use [Δ, h1, h2, proves_of_proves_bot h3],
	},
	{
		rcases ih with ⟨Δ, h1, h2, h3⟩,
		use [Δ, h1, h2, prop_thm.lem h3],
	},
end

lemma max_of_fin_chain {α : Type*} [partial_order α]
: ∀{c : set α}, c.finite → is_chain (≤) c → c.nonempty → ∃m ∈ c, ∀{b}, b ∈ c → b ≤ m :=
begin
	intros c c_fin c_chain c_nonempty,
	set P : set α → Prop := λx, (∃(x_fin : x.finite) (x_chain : is_chain (≤) x)
	 (x_nonempty : x.nonempty), true) → ∃m ∈ x, ∀{b}, b ∈ x → b ≤ m with P_def,

	have P_empty : P ∅,
	{
		rw P_def,
		intro h,
		rcases h with ⟨a, a, contra, -⟩, exfalso,
		exact set.not_nonempty_empty contra,
	},

	suffices h : P c, {exact h ⟨c_fin, c_chain, c_nonempty, true.intro⟩},
	apply set.finite.induction_on c_fin P_empty,
	intros a s has s_fin hPs,
	intro h,
	rcases h with ⟨as_finite, as_chain, as_nonemtpty, -⟩,
	have s_chain := is_chain.mono (set.subset_insert a s) as_chain,
	by_cases s_nonempty : s.nonempty,
	{
		rcases hPs ⟨s_fin, s_chain, s_nonempty, true.intro⟩ with ⟨m, hms, hm⟩,
		by_cases h : a ≤ m,
		{
			use [m, set.mem_insert_of_mem a hms],
			intros b hb,
			simp at hb,
			cases hb, {rwa hb},
			{exact hm hb},
		},
		{
			have hmas : m ∈ (insert a s) := set.mem_insert_of_mem a hms,
			have haas : a ∈ (insert a s) := set.mem_insert a s,
			have hma : m ≤ a,
			{
				unfold is_chain at as_chain,
				unfold set.pairwise at as_chain,
				by_cases m_eq_a : m = a, {rw m_eq_a},
				specialize as_chain hmas haas m_eq_a,
				tauto,
			},
			use [a, haas],
			intros b hb, simp at hb,
			cases hb,
			{rw hb},
			{
				specialize hm hb,
				exact le_trans hm hma,
			},
		},
	},
	rw set.not_nonempty_iff_eq_empty at s_nonempty,
	use [a, set.mem_insert a s], rw s_nonempty,
	intros b hb, simp at hb, rw hb,
end

lemma maximal_consistent_of_consistent {Γ} :
consistent Γ → ∃Γ', Γ ⊆ Γ' ∧ maximal_consistent Γ' :=
begin
	intro Γ_con,
	have := zorn_subset_nonempty {Γ : set prop_formula | consistent Γ} _, swap,
	{
		intros c c_ss c_chain gbg,
		use [c.sUnion],
		simp,
		split, swap, {exact λs hs, set.subset_sUnion_of_mem hs},
		by_contra c_bot,
		unfold consistent at c_bot, push_neg at c_bot,
		rcases fin_subset_proves_of_proves c_bot with ⟨Δ, Δ_ss, Δ_fin, Δ_bot⟩,
		suffices : ∃b ∈ c, b ⊢ ⊥,
		{
			rcases this with ⟨b, hb1, hb2⟩,
			have := c_ss hb1, simp at this,
			exact Γ_con (false.rec (Γ ⊢ ⊥) (this hb2)),
		},

		have : ∀p ∈ Δ, ∃ζ ∈ c, p ∈ ζ,
		{
			intros p hp,
			rcases Δ_ss hp with ⟨ζ, hζc, hpζ⟩,
			exact ⟨ζ, hζc, hpζ⟩,
		}, 
		choose f hfc hf using this,
		have sub_chain_fin := set.finite.dependent_image Δ_fin f,
		set sub_chain := {y : set prop_formula | ∃ (x : prop_formula) (hx : x ∈ Δ), y = f x hx}
		with sub_chain_def,
		have sub_chain_ss : sub_chain ⊆ c,
		{
			intros ζ hζ,
			rw sub_chain_def at hζ,
			simp at hζ,
			rcases hζ with ⟨p, hpΔ, hpf⟩,
			rw hpf,
			exact hfc p hpΔ,
		},
		have Δ_nonempty : (Δ.nonempty),
		{
			by_contra h,
			rw set.not_nonempty_iff_eq_empty at h,
			rw h at Δ_bot,
			exact empty_consistent Δ_bot,
		},
		have sub_chain_nonempty : sub_chain.nonempty,
		{
			cases Δ_nonempty with p hp,
			have : f p hp ∈ sub_chain,
			{
				rw sub_chain_def, simp,
				exact ⟨p, hp, rfl⟩,
			},
			exact set.nonempty_of_mem this,
		},
		rcases max_of_fin_chain sub_chain_fin (is_chain.mono sub_chain_ss c_chain) 
		sub_chain_nonempty with ⟨m, hmsub, hm⟩,
		use [m, sub_chain_ss hmsub],
		suffices : Δ ⊆ m, {exact proves_of_subset_proves this Δ_bot,},
		suffices : ∀p ∈ Δ, ∃b ∈ sub_chain, p ∈ b,
		{
			intros p hp,
			rcases this p hp with ⟨b, b_sub, hpb⟩,
			exact @hm b b_sub p hpb,
		},
		intros p hp,
		use [f p hp], rw sub_chain_def, simp,
		use [p, hp, rfl, hf p hp],
	},

	rcases (this Γ Γ_con) with ⟨Γ', Γ'_con, Γ'_contains, Γ'_maximal⟩,
	simp at Γ'_con,
	use [Γ', Γ'_contains],
	rw maximal_consistent_iff, use Γ'_con,
	intros Δ Δ_con, 
	rw ssubset_iff_subset_ne,
	push_neg,
	finish [Γ'_maximal Δ Δ_con],
end

theorem completeness (Γ φ) : (Γ ⊢ φ) ↔ (Γ ⊨ φ) :=
begin
	split, {exact soundness},
	suffices h : ∀Γ, consistent Γ → satisfiable Γ,
	{exact completeness_iff.mpr h}, clear Γ φ,
	intros Γ Γ_con,
	rcases maximal_consistent_of_consistent Γ_con with ⟨Γ', Γ_ss, Γ'_maxcon⟩,
	cases (satisfiable_of_maximal_consistent Γ'_maxcon) with s hs,
	use s,
	intros p hp,
	exact hs (Γ_ss hp),
end

theorem pierces_law (p q) : ∅ ⊢ (((p ->> q) ->> p) ->> p) :=
begin
	rw completeness,
	intros s hs,
	unfold value,
	tauto!,
end

end prop_logic