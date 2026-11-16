initialize();
/***  {37;done}***/

declare_package(`ind_examples);
/***  {38;done}***/

clear_event(start_ind_examples);
/***  after 0 initialization;***/

break_on_user_error[0] = 1;
/***  {39;done}***/

define start_ind_examples true;
/***  event 1 max_exps 0 net_exps 0 rules 0***/

define nat ind(nat:type){zero:nat;succ:nat=>nat};
/***  event 2 max_exps 50 net_exps 27 rules 20***/

define list (alpha:type){ind(alphalist:type){nil:alphalist;cons:alpha=>alphalist=>alphalist}};
/***  event 3 max_exps 113 net_exps 104 rules 171***/

define color ind(color:type){red:color;gtreen:color;blue:color};
/***  event 4 max_exps 39 net_exps 17 rules 37***/

define ind_equal (s:type) ind(ind_equal:s=>s=>type){id:pi(x:s){ind_equal(x,x)}};
/***  event 5 max_exps 467 net_exps 467 rules 1621***/

define kind ind(kind:type){
  nat_kind:kind;
  bool_kind:kind};
/***  event 6 max_exps 28 net_exps 12 rules 43***/

define bool_kind      kind.bool_kind;
/***  event 7 max_exps 9 net_exps 9 rules 6***/

define nat_kind        kind. nat_kind;
/***  event 8 max_exps 4 net_exps 4 rules 3***/

define exp ind(exp : kind=>type){
  nat_to_exp:nat=>exp(nat_kind);
  true:exp(bool_kind);
  false:exp(bool_kind);
  if:exp(bool_kind)=>exp(nat_kind)=>exp(nat_kind)=>exp(nat_kind);
  };
/***  event 9 max_exps 148 net_exps 99 rules 174***/
