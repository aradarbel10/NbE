pattern unification: decidable fragment of higher order unification

syntax: de bruijn indices
semantic: de bruijn levels, beta-normal

flexible: meta applied to a spine
rigid: bound var applied to a spine
neutral: value that got blocked on a var
        stuck on a bound var - no luck
        stuck on a meta - might be already solved

force: ???


bidi
```
check :: Ctx -> Raw -> VTyp -> Term
infer :: Ctx -> Raw -> (Term, VTyp)
```

```
data MetaEntry
    = MEVar Name VTyp (Maybe Value)
    | MEEq  Env (Value, VTyp) (Value, VTyp) -- Env here might contain twin types
type MCtx = ([MetaEntry], [MetaEntry]) -- zipped

data Entry
    = EVar Name VTyp
    | ETwn Name VTyp VTyp
type Ctx = [Entry]
```

mctx: context holding metavars w/ types (and possibly definitions)
    and conversion constraints, `∀Γ . (s : S) ≡ (t : T)`

twins:
    how to simplify `?Γ . (f : Π A B) ≡ (g : Π S T)`?
    NOT like `?Γ, x : A . (f x : B x) ≡ (g x : T x)` because `A, T` aren't unified YET
    instead, `?Γ, x : A‡T . (f x́ : B x́) ≡ (g x̀ : T x̀)`

flexible occurence: argument of a metavar
rigid occurence: otherwise
strong rigid: not an argument of anything

argument of a metavar: flexible
argument of a var: rigid
otherwise: strong rigid

'occurs' check: error only on strong rigid occurences


unification:
1. rigid decomposition
- η-expandable: `?Γ . (t : TCON) ≡ (t' : TCON')`
    η-expand, descend structurally into `TCON` (ex. use twins for Π, normal recursion for Σ)
- rigid-rigid: descend structurally into `t` and `t'`
    error for different constructs
    or different rigid vars
2. pruning: when `Δ, ∀Γ . α sk ≡ t` try to reduce the size of `sk`
- ensure `fvʳⁱᵍ(t) ⊆ dom(sk)`
            just regular vars!
- forall `β sp` in `fmvʳⁱᵍ(t)`, in mctx `β : T`,
    do `pruneSpine (𝚽 : Ctx) (𝚿 : Ctx) (V : {Var}) (T : VTyp) (sp : Spine)`
    (prunes `V` from `sp`)
    - traverse the pi type `T` and the arguments `sp` of it simultaneously left-to-right
      `𝚽` accumulates original parameters
      `𝚿` accumulates remaining parameters
                both initially empty
    - returned type  `U`: has only `𝚿` parameters
    - returned value `u`: `\y -> λ𝚽. y𝚿`

    - add fresh meta `γ : U` before `β`
    - solve `β ≔ uγ : T`
    - substitute `β ↦ uγ` in the entire rest of the mctx & problem
3. flexible problems
- flex-rigid:
    - shift past metadefs not occuring in problem
    - carry metadefs occuring in problem
    - shift past any other problem

    when reached the head metavar `Δ,α : A, ∀Γ. (α sp : S) ≡ (t : T)`
                                     ^  same  α  ^
    **by inversion:** unique solution if:
    - ensure 'occurs': `α ∉ fmvˢᵗʳ(t)` or fail
    - ensure `sp` is η-contractible to a pattern or block
        - just variables
        - linear (distinct) on the vars `∩ fv(t)`
    - ensure validity of `λ sp . t` or block
        - scope-correct: `α` never occurs in carried metadefs `Ξ` or in `t`
        - type-correct: solution is well typed under mctx `Δ,Ξ`
    
    otherwise try shifting left:
- flex-flex:
    when `Δ,α : T, ∀Γ. (α sp) ≡ (β sp')` and `|sp| = |sp'|`
        - first try solving for `α` by inversion
        - otherwise carry `α : T`, exchange sides, and shift left to solve for `β`
    
        - shift past metadefs not occuring in problem
        - shift past any other problem

    when `β = α`
        - ensure both spines are just variables
        - `α` must be independent of variables disagreeing
4. simplification
- η-expansion on metavars
    - when   `Δ,                               α                    : Π𝚽. Σ S T`
      expand `Δ, β : Π𝚽. S, γ : Π𝚽. T (β 𝚽), α ≔ Π𝚽. (β 𝚽, γ 𝚽) : Π𝚽. Σ S T`
      corresponds to `t =η (proj1 t, proj2 t)`
    - when   `Δ, α : Π𝚽. Π(Σ S T). U`
      expand `Δ, β : Π(xₒ : S). Π(x₁ : T x₀). U[x ↦ (x₀, x₁)], α ≔ `