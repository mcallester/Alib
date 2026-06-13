
restart_event(`schroeder_bernstein_functions);
/** {35;done} **/

declare_package(`schroeder_bernstein_functions);
/** {36;done} **/

/** ========================================================================
empty set exists
========================================================================**/

package[0]
/** {
    37;
    schroeder_bernstein_functions} **/

check_for_corruption[0] = 1;
/** {38;done} **/

proof_stepping[0] = 0;
/** {39;done} **/

intern_stepping[0] = 0;
/** {40;done} **/

current_events[0]
/** {41;} **/

break_on_user_error[0] = 0;
/** {65;done} **/

// ========= voodoo block
clear_event(sets_exist);
/** sets_exist has not been defined as an event **/

//intern_hook[0]=NULL;

// compile new code here

theorem sets_exist (foo:type){inhabited(set_of(foo))}{sorry};
/** {43;done} **/

finish_event();
/** there is no suspended event to finish **/

// ====== end of voodoo block ====

clear_event(emptyset_exists);
/** emptyset_exists has not been defined as an event **/

theorem emptyset_exists(tau:type){exists(s:set_of(tau)){empty(in(s))}
  }{
  //show{empty(in(the_set(x:tau){not(x=x)}))};
  classify(the_set(x:tau){not(x=x)})
  };
/** {44;done} **/

finish_event();
/** there is no suspended event to finish **/

int x[0]=1;
/** {45;done} **/

/** ========================================================================
preimage
========================================================================**/
/** ========================================================================
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
========================================================================**/

exp_limit[0]=500000;
/** {46;done} **/

clear_event(preimage);
/** preimage has not been defined as an event **/

define preimage(tau:type, sigma:type, y:sigma, h:tau=>sigma){
  assert(x:tau){h(x)=y}};
/** {47;done} **/

finish_event();
/** there is no suspended event to finish **/

int_exp(max_total[0])
/** {48;370} **/

clear_event(injection);
/** injection has not been defined as an event **/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/** {49;done} **/

finish_event();
/** there is no suspended event to finish **/

//int_exp(intern_hook_count[0])

//event_max_counts()
int_exp(max_total[0])
/** {50;674} **/

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/** {51;done} **/

finish_event();
/** there is no suspended event to finish **/

int_exp(max_total[0])
/** {52;674} **/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};
/** {53;done} **/

finish_event();
/** there is no suspended event to finish **/

//three versions of bijections_invert. Identical except for the
//injection proof which is modified to exhibit the issue motivating
//congruence on quantified expressions, with the last one requiring the bvars.

int_exp(max_total[0])
/** {54;850} **/

clear_event(bijections_invert);
/** bijections_invert has not been defined as an event **/

theorem bijections_invert(tau:type,sigma:type,inhabited(bijection(tau,sigma))){
  inhabited(bijection(sigma,tau))
  }{
  using(
	f:bijection(tau,sigma),
	g = lambda(x:sigma){the(y:tau){f(y)=x}},
	//intern_cps(lambd(x:sigma){...})
	///decl(x:sigma)
	////intern_cps(the(assert(y:tau){f(y)=x}))
	
	/////backchain(inhabited(assert(...)))
	//////analyze(inhabited(...))
	///////classify(f) binds a surjection variable to f
	///////yields forall(y:tau)exists(x:sigma)f(x)=y
	///////yields exists(x:sigma)f(x)=y
	///////yields the backchain goal.
	
	/////backchain(unique(assert(...)))
	//////analyze(unique(...))
	///////classify(f) binds an injection variable to f.
	///////yields forall(y:sigma){unique(assert(x:tau){f(x) = y})}
	///////yields unique(x:sigma)f(x)=y
	///////yields the backchain goal.
	
	witness(g)
	//analyze(g)
	///classify(f) generates the desired habitation and uniquenes formulas
	//classify(g) then places g under bijection which proves the goal.
	)};

finish_event();
/** there is no suspended event to finish **/

int_exp(max_total[0])
/** {56;5773} **/

clear_event(empty_uniqueness);
/** empty_uniqueness has not been defined as an event **/

theorem empty_uniqueness (tau:type) {
  unique(assert(s:set_of(tau)){empty(in(s))})}{
  show(x1:assert(s:set_of(tau)){empty(in(s))},
       x2:assert(s:set_of(tau)){empty(in(s))}){
    x1=x2}{
    show{in(x1)=in(x2)} // need these in upsilon for binding frame pulls
  }};
/** {57;done} **/

finish_event();
/** there is no suspended event to finish **/

clear_event(test_injectivity);
/** {58;done} **/

theorem test_injectivity (tau:type,sigma:type,
                          f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){
  x_2=x_3};
/** {59;done} **/

theorem Schroeder_Bernstein (
                             tau:type,
                             sigma:type,
                             inhabited(injection(tau,sigma)),
                             inhabited(injection(sigma,tau))){
  inhabited(bijection(tau,sigma))}{
  using(f:injection(tau,sigma),
        g:injection(sigma,tau),
	usef =mu assert(x:tau){not(exists(y:sigma){not(is(g(y),usef)) && g(y) = x})}){
    classify(lambda(x:tau){if(is(x,usef),f(x),the(y:sigma){g(y)=x})})}};

types_of(g(y))

types_of(usef)


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
