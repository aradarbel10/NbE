# Normalization by Evaluation
This repo contains my learning process of normalization by evaluation and advanced type checking techniques

- [NbE](https://github.com/aradarbel10/NbE/tree/master)
- [Higher Order Pattern Unification](https://github.com/aradarbel10/NbE/tree/HOPU)

## Example
```
let zero = lam f x . x                           in
let succ = lam p f x . f (p f x)                 in
let five = succ (succ (succ (succ (succ zero)))) in
let add  = lam a b s z . a s (b s z)             in
let mul  = lam a b s z . a (b s) z               in
let ten  = add five five                         in
let hund = mul ten ten                           in
let thou = mul ten hund                          in
thou"
```

## References
- [Elaboration Zoo](https://github.com/AndrasKovacs/elaboration-zoo) by the invaluable Andras Kovacs
- [Beautifully-commented example](https://discord.com/channels/633240603777433601/633240603777433603/1008392203179143249) by brendanzab
- All the peeps over at the [PLT Discord Server](http://discord.gg/4Kjt3ZE)