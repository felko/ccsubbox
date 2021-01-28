## Examples for 1/28
---------------------
```
// what is the type of map?
map := [forall T1 <: Top] [forall T2 <: Top] (f : (x : T1) -> T2) (l : {*} List[{*} T1]) -> {l} List[{l} T2]

// what is the type of list?
                /------------------------------------------------------------------------- the list here
List[T] := {T} [forall A <: Top] {T} (f : (v : T) -> {f} (a : A) -> {v, a} A)) -> {T,f} (s : A) -> {T,s} A)

// what are its constructors?
empty[T] := {T} [forall A <: Top] {T} (f : (v : T) -> {f} (a : A) -> {v, a} A)) -> {T,f} (s : A) -> s)
cons[T] := {T} (hd : T) (lst : List[T])
           {lst, hd} [forall A <: Top] {T} (f : (v : T) -> {f} (a : A) -> {v, a} A)) -> {T,f} (s : A) -> 
             ( (f hd (lst f s)) : [v := {hd}][a := {s}]{v, a} A)
// unsoundness over here         ~~~~~~~~~~~~~~~~~~~~~~^^^^^^^^

List[T] := {T} [forall C <: {*}] [forall A <: Top] {T} (f : (v : T) -> {f} (a : C A) -> C A)) -> {T,f} (s : C A) -> C A)

empty[T] := {T} [forall A <: Top] {T} (f : (v : T) -> {f} (a : A) -> {v, a} A)) -> {T,f} (s : A) -> s)
cons[T] := [forall C <: {*}] (hd : C T) (tl : C List[T]) 
                /---------------------------------- list follows here 
            [forall C1 <: {*}] [forall A <: Top]
            (f : (v : T) -> (a : C1 A) -> C1 A)) -> (s : A) -> 
             ((f hd (lst f s)) : [C1 A]

list_id = [forall C <: {*}] [forall T <: Top] (lst: List[C T]) -> lst [C][T] cons[T][C] empty
```

