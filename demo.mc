
restart_event(`initialize_alfred);

declare_package(`demo);

theorem emptyset_exists(){
  exists(s:set){not(inhabited(s))}}{
  let(s:set,empty=assert(x:s){not(x=x)}){}};

define injection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      unique(assert(x:s){y = f(x)})}
    }};

define surjection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      exists(x:s){f(x)=y}}}};

define bijection(s:set,w:set){
  assert(f:s=>w){
    is(f,injection(s,w)) && is(f,surjection(s,w))}};

theorem bijections_invert (s:set, w:set) {implies(inhabited(bijection(s,w)), inhabited(bijection(w,s)))} {
  let(f:bijection(s,w)){
    // properties needed for "the()" safety below require consider(f) hence these proofs
    show(forall(x:w){exists(y:s){f(y)=x}}){consider(f)};
    show(forall(x:w,y1:s,y2:s){((f(y1)=x) && (f(y2)=x)) |=> (y1=y2)}){consider(f)};
    //need to define g for the system
    let(g = lambda(x:w){the(y:s){f(y)=x}}){
      show(is(g,bijection(w,s))) //this line can be omitted if we have
                                 //show_existential actually run a
                                 //backtrackable show on witnesses.
      }}};

define empty_set the(s:set){not(inhabited(s))}; //fails to show uniqueness

//fails at the() safety. I can fix that with some lemmas and with
//note_reduct() and we can probably avoid needing those with system
//improvements, but then it fails for unknown reasons at this point at
//is(h,surjection(s,w))
theorem SB (s:set, w:set) {
  implies(inhabited(injection(s,w))&&inhabited(injection(w,s)),
          inhabited(bijection(s,w)))}{
  suppose(inhabited(injection(s,w))&&inhabited(injection(w,s))){
    let(f:injection(s,w),
        g:injection(w,s),
        use_f =μ lambda(x:s){
          not(exists(y:w){
                g(y)=x
                && not(exists(z:s){
                         f(z)=y && use_f(z)})})}){
      let(h = lambda(x:s){
            if(use_f(x),f(x),the(y:w){g(y)=x})}){
        show(is(h, bijection(s,w))){
          show(is(h, injection(s,w)));
          show(is(h, surjection(s,w)))}}}}};
