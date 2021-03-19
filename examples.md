x : Exc
------------------
fun () { (fun() x) } : {x} (Unit -> ({x} (Unit -> {x} Exc))) : shallow
                     : {} (Unit -> ({} (Unit -> {x} Exc))) : deep

fun () { fun (k) (k x) } -- x should be captured here.

List[T <: {*} Top] = {?} ((f : ...) -> ({?, f} (initial : ...) -> ({?, f, initial} A))) : shallow
                     {} ((f : ...) -> ({} (initial : ...) -> ({?, f, initial} A))) : deep

{ capture T } LazyList[A] 

f : (elem : T) -> (accum : A) -> {elem, accum} A

ascribing capture sets to type variables
----------------------------------------
cv(forall A <: {*} Top, (first : A) -> (second : A) -> {first, second} A) = {}

A <: {*} Top
-------------
cv((first : A) -> (second : A) -> {first, second} A) = {}) = {}

A <: {*} Top
first : A
---------------
cv((second : A) -> {first, second} A) = {first}


--------------------------------------------------
[A <: {*} Top] -> (first : A) -> (second : A) -> A  --- cv should be {}
        A = {*}                                 {*}     cv could be {*} 


A <: {*} Top, first : A, 
-------------------------------------
(second : A) -> A --- cv should be {*} (could be first)
                      cv could be ???
                      cv could be {A} ???

(second : A) -> first -- term