restart_event(`Kurt_init);
/** {30;done} **/

declare_package(`schroeder_bernstein_functions);
/** {31;done} **/

/** ========================================================================
We assume that each undo frame is associated with a context --- a set of variable
declarations and assumptions.

We define a user-context to be a context (and assiciated undo frame) where
the only contrained variables are explicitly constrained by user assumptions.

Inference by Conservative Extension: A conservative extension of a
an undo_frame F is a successor undo frame G with the property
that any formula Phi in the context of frame F that is entailed
in the context of G is also entailed in the context of frame F.

To form a conservative extension we introduce a variable <x:tau>
which is not in the context of F and constrain <x:tua> is a way that
allows additional inferences about expressions that are in_context in the frame F.

A primary example is binding. Here we have an interned expression e and we have proved is(e,tau)
in frame F.  In this case frame G can construct or find an out-of context variable <x:tau>
and assert <x:tau> = e.  This will cause all lemmas and functions defined on the type tau
to be effectively instantiated with e.  Any formula proved under this extension that was in-context
and interned in the pevious frame can them be "promoted" from G to F when G is popped.
Bindings can generate both formula Phi[e] by universal instantiation and also formulas of the form
Exists(x:tau)Phi[x] where e is serving as the witness of the existential.

A second example of inference by conservative extension occurs when F entails exists(x:tau)Phi[x].
In this case G can extend the context with a variable <x:tau> not in the context F
and assert Phi[<x:tau>].

The set of interned and safe in_context non-variable expressions e define a set of
of binding extensions and the set of interned and proved existential formulas
defines a set of existential extensions.  Rather than make extensions of extensions
we can iterate through the extensions adding variaous inferences to the frame F.
========================================================================**/

define injection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      unique(assert(x:s){y = f(x)})}
    }};
/** {32;done} **/

define surjection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      exists(x:s){f(x)=y}}}};
/** {33;done} **/

define bijection(s:set,w:set){
  assert(f:s=>w){
    is(f,injection(s,w)) && is(f,surjection(s,w))}};
/** {34;done} **/

theorem Schroeder_Bernstein{
  s:set,
  w:set,
  inhabited(injection(s,w)),
  inhabited(injection(w,s)),
  show inhabitred(bijection(s,w)){
    f:injection(s,w),
    g:injection(w,s),
    usef =μ lambda(x:s){
      not(exists(y:w){
	    g(y)=x
	    && not(exists(z:s){
		     f(z)=y && usef(z)})})}
    h = lambda(x:s){if(usef(x),f(x),the(y:w){g(y)=x})}}
  };
/** {
    in context;
    illegal syntax for theorem assertion} **/

/** ========================================================================

In the SB example the first challenge to is to check the safety of the(y:w){g(y)=x}
in the definition of h.
The context here
includes all of the expressions in the preceding definitions, the normal forms of all
the formulas involved, the fixed point equation usef = lambda(x:s){...}, the declaration x:s,
and the assumption not(usef(x)).

Assuming the mu rule we have that not(usef(x)) implies exists y:w g(y)=x && ... which implies
exists(y:w) g(y)=x by existential propagation.

The next challenge is to show that h is a bijection. By backchaining we will try to show
that h is an injection and that h is a surjection.

Injection case: For the injection case we must
show forall(x1:s,x2:other_than(s,x1))) h(x1) != h(x2). Since we have normal forms we have now interned both
if(usef(x1) ...) and if(usef(x2) ...). This leads to a four fold case analysis on
usef(x1) and usef(x2).

In the case where usef(x1) and usef(x2) we get f(x1)=f(x2) which contradicts injectivity of f.
In the case of usef(x1) and not(usef(x2)) assume h(x1)=h(x2) which gives f(x1) = the(y:w){g(y)=x2). It also gives
not(exists(z:s){f(z) = f(x1)} && usef(z)}. But x1 is a witness.

Similarly for not(usef(x1)) and usef(x2).

For not(usef(x1)) and not(usef(x2)) assume the(y:w){g(y)=x1} = the(y:w){g(y)=x2).  This implies x1=x2
by the injectivity of g.

For the surjective case we consider y:w and want to show exists(x:s) h(x)=y.  We consider g(y) as a witness.
We want to show h(g(y)) = y.  We focus on h(g(y)) and case on usef(g(y)).

========================================================================**/








