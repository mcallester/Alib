
restart_event(`schroeder_bernstein_functions);

declare_package(`schroeder_bernstein_functions);

/** ========================================================================
empty set exists
========================================================================**/

package[0]

check_for_corruption[0] = 1;

proof_stepping[0] = 0;

intern_stepping[0] = 0;

current_events[0]

break_on_user_error[0] = 1;

// ========= voodoo block
clear_event(sets_exist);

//intern_hook[0]=NULL;

// compile new code here

theorem sets_exist (foo:type){inhabited(set_of(foo))}{sorry};

finish();
/** there is no suspended event to finish **/

// ====== end of voodoo block ====

clear_event(emptyset_exists);
/** emptyset_exists has not been defined as an event **/

theorem emptyset_exists(tau:type){exists(s:set_of(tau)){empty(in(s))}
  }{
  //show{empty(in(the_set(x:tau){not(x=x)}))};
  classify(the_set(x:tau){not(x=x)})
  };

clear_event(preimage);

//do the next two the first time

//int intern_hook_count[0]=0;

//set_intern_hook(mze){if(mze->constructor==conservative){intern_hook_count[0]++;}};
//set_intern_hook(mze){intern_hook_count[0]++;};

//do the next two the second time (after clearing preimage).

//int num_desired[0]=10;

//set_intern_hook(mze){
//  if(intern_hook_count[0] && (random()%intern_hook_count[0])<num_desired[0]){
//    mcpprint(sugar(mze));}
//  };

exp_limit[0]=500000;

define preimage(tau:type, sigma:type, s:set_of(tau), w:set_of(sigma), y:in(w), h:in(s)=>in(w)){
  assert(x:in(s)){h(x)=y}};

clear_event(injection);

define injection(tau:type,sigma:type,s:set_of(tau),w:set_of(sigma)){
  assert(f:in(s)=>in(w)){
    forall(y:in(w)){
      unique(preimage(tau,sigma,s,w,y,f))}}};

//int_exp(intern_hook_count[0])

//event_max_counts()

define surjection(tau:type,sigma:type,s:set_of(tau),w:set_of(sigma)){
  assert(f:in(s)=>in(w)){
    forall(y:in(w)){
      inhabited(preimage(tau,sigma,s,w,y,f))}}};

define bijection(tau:type,sigma:type,s:set_of(tau),w:set_of(sigma)){
  assert(f:in(s)=>in(w)){
    is(f,injection(tau,sigma,s,w)) && is(f,surjection(tau,sigma,s,w))}};

//three versions of bijections_invert. Identical except for the
//injection proof which is modified to exhibit the issue motivating
//congruence on quantified expressions, with the last one requiring the bvars.

theorem bijections_invert(tau:type,sigma:type,s:set_of(tau), w:set_of(sigma)){
  inhabited(bijection(tau,sigma,s,w)) |=> inhabited(bijection(sigma,tau,w,s))
  }{
  using(f:bijection(tau,sigma,s,w),
        g = lambda(x:in(w)){the(y:in(s)){f(y)=x}}){
    show{is(g,injection(sigma,tau,w,s))}{
      show(y:in(s), x1:assert(x:w){g(x)=y}, x2:assert(x:in(w)){g(x)=y}){x1=x2}{
        show{f(y)=x1}{classify(x1)};
        show{f(y)=x2}{classify(x2);};};
      classify(g)};
    show{is(g,surjection(sigma,tau,w,s))}{
      show(x:s){is(f(x), preimage(tau,sigma,w,s,x,g))};};
    show{is(g,bijection(sigma,tau,w,s))}; 
    }};

clear_event(empty_uniqueness);

theorem empty_uniqueness (tau:type) {
  unique(assert(s:set_of(tau)){empty(in(s))})}{
  show(x1:assert(s:set_of(tau)){empty(in(s))},
       x2:assert(s:set_of(tau)){empty(in(s))}){
    x1=x2
      }};

theorem test_injectivity (tau:type,sigma:type,s:set_of(tau), w:set_of(sigma), 
                          f:injection(tau,sigma,s,w), x_2:in(s), x_3:in(s), f(x_2)=f(x_3)){
  x_2=x_3}{
  classify(f(x_2)); classify(x_3); classify(x_2)};

theorem Schroeder_Bernstein (
                             tau:type,
                             sigma:type,
                             s:set_of(tau),
			     w:set_of(sigma),
			     inhabited(injection(tau,sigma,s,w)),
			     inhabited(injection(sigma,tau,w,s))){
  inhabited(bijection(tau,sigma,s,w))}{
  using(
	f:injection(tau,sigma,s,w),
	g:injection(sigma,tau,w,s),
	usef =mu(x:in(s)){not(exists(y:in(w)){not(is(g(y),in(usef))) && g(y) = x})}){
    classify(lambda(x:in(s)){if(is(x,in(usef)),f(x),the(y:in(w)){g(y)=x})})}};

//WORKING PROOF OF INJECTION SUPERSEDED ABOVE
// injection works but needs exploration. Also still want to try the() and taxonomic
theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  with(f:injection(s,w),
       g:injection(w,s),
       use_f =μ lambda(x:s){
         not(exists(y:preimage(w,s,x,g)){
               not(exists(z:preimage(s,w,y,f)){
                     use_f(z)})})}){
    with(h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
      show(){is(h,injection(s,w))}{
        show(x:s){use_f(x) |=> f(x)=h(x)};
        show(x:s){not(use_f(x)) |=> the(y:w){g(y)=x}=h(x)};
        show(y:w){unique(preimage(s,w,y,f))};
        show(x:s){unique(preimage(w,s,x,g))};
        
        //show(x:s){is(preimage(w,s,x,g),w)}; need guidance on this
        
        show(x:s, //apply fixed point of use_f
             not(use_f(x)),
             y:preimage(w,s,x,g),
             xx:preimage(s,w,y,f)){
          not(use_f(xx))}{
          with(yy:assert(yyy:preimage(w,s,x,g)){
                 not(exists(xxx:preimage(s,w,yyy,f)){use_f(xxx)})}){
            show{yy=y}{with(focus(y), focus(yy))};}};
        
        //explore why this doesn't eliminate the body in show_case_contradictory
        //show(x:s,
               //   not(use_f(x))){
          //forall(y:preimage(w,s,x,g)){
            //  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
        show(x_1:w,
             x_2:preimage(s,w,x_1,h),
             x_3:preimage(s,w,x_1,h)){
          x_2 = x_3
          }{
          show_case_contradictory(use_f(x_2) && not(use_f(x_3))){
            with(focus(x_3), focus(x_1), focus(x_2)){
              //show{forall(y:preimage(w,s,x_3,g)){
                  //  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
              show{forall(y:preimage(w,s,x_3,g)){
                  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
              }};
          show_case_contradictory(use_f(x_3) && not(use_f(x_2))){
            with(focus(x_3), focus(x_1), focus(x_2))};
          with(assume_not_goal,focus(x_2), focus(x_3)){
            show_case(use_f(x_3))}}};
      show(){is(h,surjection(s,w))}{
        show(x1:w){exists(x2:s){h(x2)=x1}}{
          show_case(use_f(g(x1))){
            with(focus(g(x1)),
                 z:assert(x2:s){f(x2)=x1},
                 focus(z))}}}}}};


//trying ontic approach
theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  
  with(f:injection(s,w),
       g:injection(w,s),
       covered_by_g =μ lambda(y:w){
         not(inhabited(preimage(s,w,y,f))) 
         || exists(yy:w){covered_by_g(yy) && y=f(g(yy))}}){
    show(x:s,covered_by_g(f(x))){ //the() safety for defining h()
      inhabited(preimage(w,s,x,g))}{
      with(focus(f(x)), //needed to avoid existence supposition for y:
           y:assert(yy:w){covered_by_g(yy) && f(x)=f(g(yy))}){
        show{is(y,preimage(w,s,x,g))}{
          show{x=g(y)}{with(focus(g(y)))};};}};
    with(uses_g = lambda(x:s){exists(y:preimage(w,s,x,g)){covered_by_g(y)}},
         h = lambda(x:s){if(uses_g(x),
                            the(preimage(w,s,x,g)),
                            f(x))}){
      show(){is(h,injection(s,w))}{
        show(y:w,
             x_2:preimage(s,w,y,h),
             x_3:preimage(s,w,y,h)){
          x_2=x_3}{
          show_case(uses_g(x_2)){
            show{unique(preimage(w,s,x_2,g))}{with(focus(x_2))};
            show{h(x_2)=the(preimage(w,s,x_2,g))};
            show{h(x_2)=y};
            show{covered_by_g(y)};
            show_case(not(uses_g(x_3))){
              
              };
            with(focus(x_2),focus(x_3))
            };
          show_case(not(uses_g(x_2)));}};}}};

//not used below here, obsolete
define inverse(s:set,w:set,f:bijection(s,w)){
  assert(g:bijection(w,s)){
    forall(x:w){f(g(x))=x} &&
    forall(y:s){g(f(y))=y}}};

theorem inverses_exist (s:set, w:set, f:bijection(s,w)){
  inhabited(inverse(s,w,f))}{
  let(g = lambda(x:w){the(y:s){f(y)=x}}){
    lemma{show(is(g,bijection(w,s)))}}
  };
