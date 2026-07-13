load_mode[0] = 1;
/** {33;done} **/

declare_package(`functions);
/** {34;done} **/

clear_event(start_functions);
/** after 0 initialization; **/

define start_functions true;
/** event 1 max 0 net 0 **/

where();
/** {after 0 initialization;} **/

clear_event(preimage);
/** the event preimage is not present **/

define preimage(sigma:type, tau:type, y:tau, f:sigma=>tau){
  assert(x:sigma){f(x)=y}};
/** event 1 max 354 net 354 **/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/** event 2 max 922 net 275 **/

theorem test_injectivity (tau:type,sigma:type,
                          f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){ 
  x_2=x_3}{
  classify(f(x_3)) //realize that f(x_3) has a unique preimage under f
  };
/** event 3 max 1825 net 221 **/

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/** event 4 max 1957 net 177 **/

clear_event(bijection);
/** the event bijection is not present **/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};
/** event 5 max 2348 net 122 **/

theorem bijections_exist(sigma:type,tau:type){
  inhabited(bijection(sigma,tau))};
/** event 6 max 2535 net 29 **/

define bij_inverse(tau:type,sigma:type,f:bijection(sigma,tau)){
  the(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}};
/** event 7 max 2939 net 613 **/

theorem bij_inverse_Thm1(tau:type,sigma:type,f:bijection(sigma,tau)){
  is(bij_inverse(f),bijection)};
/** event 8 max 3585 net 120 **/

clear_event(permutation);
/** the event permutation is not present **/

define permutation(sigma:type){bijection(sigma,sigma)};
/** event 9 max 117 net 117 **/

define composition(sigma:type,tau:type,gamma:type,f:tau=>gamma,g:sigma=>tau){lambda(x:sigma){f(g(x))}};
/** event 10 max 9600 net 289 **/

theorem permutation_composition (s:type,f:permutation(s),g:permutation(s)){is(composition(f,g),permutation(s))};
/** event 11 max 453 net 453 **/

define idfun(s:type){lambda(x:s){x}};
/** event 12 max 31 net 31 **/

theorem permutation_inverse(s:type,f:permutation(s)){composition(f,bij_inverse(f)) = idfun(s)};
/** event 13 max 261 net 115 **/
