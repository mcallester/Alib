
reinitialize();

/** ========================================================================
functions starts form initialization
========================================================================**/

//load_mode[0] = 1;

declare_package(`functions);

clear_event(start_functions);

define start_functions true;

exp_limit[0] = 100000;

/** ========================================================================

========================================================================**/
define identity(sigma:type){lambda(x:sigma){x}};

define preimage(sigma:type, tau:type, y:tau, f:sigma=>tau){
  assert(x:sigma){f(x)=y}};

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};

theorem injection_thm1 (tau:type,sigma:type,
                        f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){ 
  x_2=x_3}{
  classify(f(x_3)) //realize that f(x_3) has a unique preimage under f
  };

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};

clear_event(bijections_invert);

theorem bijections_invert(tau:type,sigma:type,f:bijection(sigma,tau)){
  exists(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}
  }{
  using(g =def lambda(x:tau){the(y:sigma){f(y)=x}}){
    show(x:sigma){g(f(x)) = x}; //backchaining from the goal and witness would do this
    witness(g)
    }};

clear_event(bij_inverses_unique);

theorem bij_inverses_unique(tau:type,sigma:type,f:bijection(sigma,tau)){
  unique(assert(g:tau=>sigma){forall(x:sigma){g(f(x))=x}})}{
  show(g1:assert(g:tau=>sigma){forall(x:sigma){g(f(x))=x}},
       g2:assert(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}){g1=g2}{
    show(y:tau){g1(y)=g2(y)}{
      using(x:preimage(y,f));};}
  };

clear_event(bij_inverse);

define bij_inverse(tau:type,sigma:type,f:bijection(sigma,tau)){
  the(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}};

clear_event(bij_inverse_implementation);

theorem bij_inverse_implementation(
				   tau:type,
				   sigma:type,
				   f:bijection(sigma,tau),
				   g1 =def lambda(y:tau){the(preimage(y,f))},
				   g2 =def bij_inverse(f)){
  g1 = g2}{
  show(y:tau){g1(y) = g2(y)} //should be immediate from backchaining.
  };

clear_event(bij_inverse_thm1);

theorem bij_inverse_thm1(tau:type,sigma:type,f:bijection(sigma,tau)){
  is(bij_inverse(f),bijection)}{
  using(g =def lambda(y:tau){the(preimage(y,f))}){
    show(x:sigma){inhabited(preimage(x,g))}{classify(f(x))};
    witness(g)}
  };

theorem bij_preimage_thm(tau:type,sigma:type,f:bijection(sigma,tau),x:tau){
  inhabited(preimage(x,f)) && unique(preimage(x,f))};

define composition(sigma:type,tau:type,gamma:type,f:tau=>gamma,g:sigma=>tau){lambda(x:sigma){f(g(x))}};

define id_fun(s:type){lambda(x:s){x}};

clear_event(bij_inverse_thm2);

theorem bij_inverse_thm2 (s:type,u:type,f:bijection(s,u)){
  composition(bij_inverse(f),f) = id_fun(s) && composition(f,bij_inverse(f)) = id_fun(u)};

clear_event(bij_composition_thm);

theorem bij_composition_thm (s:type, u:type, v:type, f:bijection(u,v), g:bijection(s,u)){
  is(composition(f,g),bijection)
  }{
  show(z:v){inhabited(preimage(z,composition(f,g)))}{
    using(pre1 =def the(preimage(z,f))){
      classify(pre1);
      witness(the(preimage(pre1,g)))}};
  show(z:v){unique(preimage(z,composition(f,g)))}{
    show(x1:preimage(z,composition(f,g)),
         x2:preimage(z,composition(f,g))){x1=x2}{
      show{g(x1)=g(x2)}}}
  };

clear_event(permutation);

define permutation(sigma:type){bijection(sigma,sigma)};

theorem permutation_thm1 (s:type,f:permutation(s),g:permutation(s)){is(composition(f,g),permutation(s))};

theorem permutation_thm2(s:type,f:permutation(s)){composition(f,bij_inverse(f)) = id_fun(s)};

clear_event(associative);

define associative(s:type){
  assert(f:s=>s=>s){
    forall(x:s,y:s,z:s){
      f(x,f(y,z))=f(f(x,y),z)}}};

clear_event(perm_composition);
define perm_composition(s:type,f:permutation(s),g:permutation(s)){composition(s,s,s,f,g)};//{lambda(x:s){f(g(x))}};

clear_event(composition_of_perms);

theorem composition_of_perms(s:type, p1:permutation(s), p2:permutation(s)){is(perm_composition(p1,p2), permutation(s))};

//needed to get the arrow type for op required in the next theorem
//permutation(s)=>(permutation(s)=>permutation(s))
theorem composition_of_perms2(s:type, p:permutation(s)){
  is(perm_composition(s,p), permutation(s)=>permutation(s))};

clear_event(composition_assoc_perms);

theorem composition_assoc_perms(s:type){is(perm_composition(s), associative(permutation(s)))}{ /*  */
  using(op =def perm_composition(s)){
    show(px:permutation(s),
         py:permutation(s),
         pz:permutation(s)){op(px,op(py,pz)) = op(op(px,py),pz)}}};

clear_event(id_is_a_perm);

theorem id_is_a_perm(s:type){is(id_fun(s), permutation(s))}{
  //show(z:s){unique(preimage(z,id_fun(s)))};
  //show(z:s){inhabited(preimage(z,id_fun(s)))};
  classify(id_fun(s))};

