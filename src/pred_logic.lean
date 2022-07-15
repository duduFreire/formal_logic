import tactic 
import tactic.induction

namespace pred_logic 

universe u

structure language (α β : Type u) :=
(hαβ : α ≠ β)
(rel_symbols : set α)
(func_symbols : set β)
(rel_arity : α → ℕ)
(func_arity : β → ℕ)

inductive term {α β : Type u} (𝓛 : language α β)
| var : ℕ → term 
| func {f : β} (f ∈ 𝓛.func_symbols) : (fin (𝓛.func_arity f) → term) → term

inductive formula {α β : Type u} (𝓛 : language α β)
| bot : formula
| relation {R : α} (R ∈ 𝓛.rel_symbols) : (fin (𝓛.rel_arity R) → term 𝓛) → formula
| Exists : ℕ → formula → formula 
| imp : formula → formula → formula

variables {α β : Type u} {𝓛 : language α β}

def term_vars : term 𝓛 → ℕ → Prop 
| (term.var m) n := m = n 
| (term.func f hf terms) n := ∃m : (fin (𝓛.func_arity f)), term_vars (terms m) n

def free_vars : formula 𝓛  → ℕ → Prop
| formula.bot m := false
| (formula.Exists n φ) m := m ≠ n ∧ free_vars φ m
| (formula.imp φ ψ) m := free_vars φ m ∨ free_vars ψ m
| (formula.relation R hR terms) m := ∃n : (fin (𝓛.rel_arity R)), term_vars (terms n) m

structure interpretation (𝓛 : language α β) :=
(domain : Type)
(to_func : ∀{f}, f ∈ 𝓛.func_symbols → (fin (𝓛.func_arity f) → domain) → domain)
(to_rel : ∀{R}, R ∈ 𝓛.rel_symbols → (fin (𝓛.rel_arity R) → domain) → Prop)

variable {M : interpretation 𝓛}

def assignment (M : interpretation 𝓛) := ℕ → M.domain

def replace (s : assignment M) (n : ℕ) (m : M.domain) : assignment M :=
λk, if k = n then m else s k

lemma replace_pos {s : assignment M} {n : ℕ} {m : M.domain}
: replace s n m n = m := if_pos rfl

lemma replace_neg {s : assignment M} {n : ℕ} {m : M.domain} {k : ℕ}
: k ≠ n → replace s n m k = s k := λhk, if_neg hk

def value (s : assignment M) : term 𝓛 → M.domain
| (term.var n) := s n
| (term.func f hf terms) := let v := λk, value (terms k) in M.to_func hf v

def satisfies : assignment M →  formula 𝓛 → Prop
| s (formula.bot) := false
| s (formula.relation R hR terms) := M.to_rel hR (value s ∘ terms)
| s (formula.imp φ ψ) := satisfies s φ → satisfies s ψ
| s (formula.Exists n φ) := ∃(m : M.domain), satisfies (replace s n m) φ

example {s s' : assignment M} {u : term 𝓛} :
(∀n, term_vars u n → s n = s' n) → value s u = value s' u :=
begin 
	intro h,
	induction' u with u f g g_func g_args ih,
	{exact h u rfl},
	{
		unfold value,
		simp,
		apply congr_arg,
		sorry,
	},
end

lemma satisfies_of_agree_free {s s' : assignment M} (φ : formula 𝓛) : 
(∀{n}, free_vars φ n → s n = s' n) → satisfies s φ → satisfies s' φ :=
begin 
	intros agree_free hsφ,
	induction' φ,
	{exfalso,exact hsφ},
	{
		unfold satisfies at *,
		sorry,
	}, repeat {sorry},
end

end pred_logic