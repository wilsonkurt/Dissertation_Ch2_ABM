;;NOTES ON WORLD
;;A) To make all worlds and setups comparable, we standardize the intrinsic quality of patch across setups by the patch value producing 'average' or 'normal' fitness benefits.
;;   We treat a patch with productivity = 3300 as the productivity at which an individual would accrue 'normal' or 'average' fitness benefits. This allows for low and high
;;   abundance setups to have patches that, on average, produce greater or less than normal fitness benefits. Productivity of a patch > 3300 = a boon to fitness whereas
;;   productivity < 3300 = a detriment to normal fitness.
;;B) All worlds are setup with 100 patches of equal size. This allows for variation in total population to alter population density. Patch size is not explicitly linked to particular spatial extents,
;;   but is interpreted as the amount of space necessary to support a group of individuals.
;;C) Toroidal wrapping is turned on in all world setups. Current application follows IFD theory and does not implement a movement cost, so individuals may move anywhere that is not defended. Future
;;   extensions applying a movement cost may warrant removal of toroidal wrapping.
;;D) Population of 1100 replicates the mean (50% quantile) total population density of 11 / sq km from Binford.

;;NOTES ON RESOURCE CHARACTERISTICS
;;A) Allee Effect: this is the number of individuals beneficial for producing a resource. Here it is controlled by the maximum beneficial group size (max_allee_size). We don't/can't vary the scale of allee increase
;;as it stands - just the number of agents who are needed. We could probably figure out a way to do this but it is not a factor within the Greene and Stamps 2001 allee formula.
;;B) Predictability: this is whether patches remain constant over time or not. There are several ways we could conceive of this - but here it is implemented as the percent of patches that change productivity each turn.
;;When completely predictable - no patches change. When completely unpredictable - the productivity is redistributed every turn. When in-between, the chosen % of patches swap productivity with each other.
;;C) Defense.Cost: this is how easy or hard it is to defend the resources on an individual's patch. Here this is the cost to returns if an agent(s) choose to defend the resource patch.
;;   the cost calculated is the cost in terms of suitability for 1 agent to defend the patch. So a defense cost of 5, means the cost to the benefit to fitness (S) for 1 agent defending a patch is 5 times worse than the mean
;;   patch S of 1.
;;D) Heterogeneity/Clustering: This is the spatial distribution of resources in the environment. While there is some debate on abundance vs heterogeneity in literature, there are some differences.
;;Here this is the heterogeneity of the environment, implemented as the amount of world productivity distributed to each cell randomly during setup. This can be thought of as how clustered resources are within a patch.
;;Note that heterogeneity and Defense.Cost are different here (though some scholars use the term interchangeably). The reason they are separated here is one is capturing spatial distribution while the other is capturing
;;ease of defense. For example, a herd of bison might be spatially clustered together but not easily defended.
;;E) Population Density: this is the relative density of individuals on the landscape. As the number of patches does not change, population density is controlled by the starting population. We hold pop density constant.
;;F) Abundance: this is the mean amount of resources available per patch in the landscape. It interacts with heterogeneity, but abundance itself is setting the returns to individual relative to the normal fitness benefit.
;;Landscapes with high abundance represent large boons to fitness and vice versa.

;;NOTE ON DENY STRATEGY CODE
;;There is code in here for a 'deny' strategy. This is left in for use in future extensions / if a user of this model is interested in it. The code does not impact the current analyses looking at egalitarian and
;;non-egalitarian outcomes. The deny strategy may be reimplemented by adding "Deny" to the list of strategy options for assignment in the 'set strategy one-of ["Free" "UA"]' code in the make-agents procedure.
;;The deny strategy is an egalitarian denial whereby all agents on the patch will defend / contribute to defense equally - so denial of access to joiners happens but with no intra-group inequality.
;;Significant research suggests this strategy should be (and is) susceptible to free-riding (prob-free-ride slider), therefore the probability of free-riding impacts this egalitarian denial strategy. Free-riding does not
;;impact the unequal access strategy as research suggests leaders and/or patrons may address free-riding and collective action (see main text).

;;THE GREENE AND STAMPS EQUATION 1:
;S = q - b(d-m)^2. We are implementing this as below where:
;S is the suitability of the patch with all factors considered
;q = instrinsic habitat quality impact on reproductive success (productivity / productivity)
;d = conspecific density in patch (#turtles on the patch)
;m = density of conspecifics at which individual reproductive success is maximized (max allee size)
;b = parameter to standardize range of (d-m)^2 to be the same as q ((0 - max_allee_size)^2)
;Equation is:
;S = (productivity / 3300) - (((count-turtles-here - max_allee_size) ^ 2) / (0 - max_allee_size) ^ 2); we do productivity/3300 because 3300 is the average productivity value.
;;;;;;;;;;;;;;;;;;;;;


globals [;;information accessible by everything
  worldprod ;;the total amount of productivity distributed into the world.
  turtles_per_turn ;;list of the number of turtles alive at the start of each turn
  patches_per_turn ;;list of the number of occupied patches at the end of each turn
  final-turns-alive-list ;;complete list of the number of turns each turtle was alive
  num_moved ;; a counter of hte number of turtles that move during the turn
  percent_moved_list ;;a list of the number of turtles that moved on each turn
  avg_percent_moved ;;a final calculation of the average proportion of turtles who moved on each turn
  avg-group-size;; the average number of turtles on occupied patches (average group size) across the model run
  group-list;; list of the number of turtles on each occupied patch
  med-group-size;; the median number of turtles on occupied patches across the model run
  b;;parameter used to get ((number turtles on patch - max_allee_size) ^ 2) into a 0 - 1 range
  running-avg-group-size ;;a list of the average group size on occupied patches per tick
  max_sust_yield_size ;;a calculation of the maximum sustainable group size on the most productive patch at setup
  add.prod ;;the amount of the total world productivity added to randomly chosen patches during resource distribution in setup
  def.cost ;;this is the cost to defend, set by the Defense.Cost chooser. Defense cost is the amount of suitability lost if a single agent defends a patch. def.cost is split among any non-free-riding defenders.
  perc-changed-on-turn ;;percent of all turtles changing their strategy at the end of the turn
  c ;;the joiner cost given to a leader/patron by a follower/client. Joiners lose c from suitability while leaders/patrons gain c * count of joiners.
  mean-patch-prod ;;the productivity of the mean patch. In a mid abundance setup, this is 3300
  intra-turn;;a recorder to mark how many moves have happened within each tick
  ;prob-free-ride;;the probability an agent will free-ride if they are playing the Deny strategy
  variable-combo
  population_size;;the number of agents to populate the world with
  max_allee_size;;the number of agents at which suitability is optimized in the model run. May be 11, 16, or 20 depending on model setup.
  pred-prob;;a probability each patch will be predictable / consistent for the next turn, set by Predictability chooser
  proportion_UA;; a running list of the percent of agents playing the UA strategy per turn
  proportion_Free;; a running list of the percent of agents playing the Free strategy per turn
]

patches-own [;; variables/information that all patches posses
  productivity;;max productivity a patch can have (prior to Allee effects)
  suitability;;what a turtle gets from residing on the patch
  time_occupied;;the combined length of time turtles have been on the patch
  exp_suit;;what a turtle could expect to get by joining the patch
  sust_turts;;a count of the number of turtles on the patch if the patch is above msy
  not_sust_turts;;a count of the number of turtles on the patch if the patch is below msy
  unpredictable ;;whether on a given turn a patch will keep its productivity or not
  return-prod ;;a placeholder value for a patch that is swapping productivity in the somewhat predictable scenario
  swap-patch ;;a signifier used during the somewhat predictable scenario so patches know which other patch they are swapping productivity with. Swapping productivity keeps the heterogeneity and total
  ;;abundance of productivity in the world the same while allowing resources to be unpredictable
  defended ;;a 0 or 1 record of if the patch is defended on this turn (1) or not (0). All patches begin as not defended.
  num_turts ;; a count of the number of turtles on the patch at the end of the turn
  turtle-strat ;;the strategy of the first turtle on a patch each turn - sets the strategy to be employed on the patch
  last-turn-strat
  exp_suit_noc ;;expected suitability for a UA patch without the join cost applied
]

turtles-own [ ;;variables/information that all turtles posses
  resources
  target;;patch with highest expected suitability
  time-in-place ;;a counter for how many ticks a turtle has resided on the current patch
  band-size-list ;;a list of the number of individuals on the same patch as a turtle at the end of each turn (band size)
  avg-band-size ;;the average band size over the life of the individual turtle
  strategy ;;the strategy an agent will employ - either egalitarian or non-egalitarian
  defender ;;a "Y" or "n" record of if the agent defended the patch it is on. Resets each turn.
  changed-strat ;;a "y" or "n" record of if the agent changed its strategy at the end of the turn. Resets each turn.
  UA-role ;;if a turtle is Leader/Patron or a Follower/Client on a given turn
  resource-per-turn-list;;a list of the resources received on each turn within each tick. This resets at each new tick.
  moves ;;number of moves per turn
]

to setup
	clear-all ;;start everything clean when click setup button
  set-worldprod
  set-allee-effect
  ask patches [set productivity 0]
  ask patches [set defended 0]
  set c Leader-Patron_Cost;;set the join cost (and kick-back to leader/patron) at 10%. This means UA will always favor a minimum of 1 person beyond max_allee optimal size on the average patch (suit of 1) and more than 1 on better patches.
  make-agents ;;make the turtles
  distribute-productivity;;run distribute productivity code to get the landscape setup
  color-patches;;run a procedure to set the patch color
  set-defense-cost
  set-predictability-probability
  setup-reporters ;;set the reporter values/starting points for recording
  set-variable-combo
	reset-ticks ;;start ticks at 0 when hit setup
end

to set-worldprod
  if Abundance = "Low Abundance" [set worldprod 170000]
  if Abundance = "Mid Abundance" [set worldprod 330000]
  if Abundance = "High Abundance" [set worldprod 570000]

  set mean-patch-prod 3300 ;;everything is build relative to a mean patch of 3300. 3300 is representing the mean value of the resource. So a patch of 3300 productivity represents a patch providing no net positive or negative
  ;;impact on relative fitness (S). It is providing the mean fitness benefit. Patches above or below that productivity level produce increased or decreased fitness.
end

to set-allee-effect
;this is a global submodel establishing the allee size value based upon the Binford dataset.
  if Allee-Effect = "Small" [set max_allee_size 11]
  if Allee-Effect = "Medium" [set max_allee_size 16]
  if Allee-Effect = "Large" [set max_allee_size 20]
end

to distribute-productivity
  set b ((0 - max_allee_size) ^ 2)
  ifelse (Heterogeneity = "Homogeneous") ;;chooser is on homogeneity or not
    [  ask patches [;; if world is homogeneous - set all patches to 3300 productivity
        set productivity worldprod / count patches
      ]
  ]
    [  ;; if world is heterogeneous, set patch productivity values based on the chooser

    set-heterogeneity;;run the set-heterogeneity sub-model for setting the appropriate values for productivity distribution to match observed NPP standard deviations

    ask patches [
    while [worldprod > 0] [
      ask one-of patches [
        set productivity productivity + add.prod ;;add the add.prod value to the randomly chosen patch. This sets the variance in distribution of resources.
        set worldprod worldprod - add.prod;;Take the add.prod value away from worldprod each time until worldprod = 0.
        ]
      ]
    ]
  ]
  ask patches  [
        set suitability (productivity / mean-patch-prod) - (((count turtles-here - max_allee_size) ^ 2) / b) ;;set suitability to be the returns a turtle would get as the first turtle on a patch. Standardized on mean patch of 3300.
        set exp_suit (productivity / mean-patch-prod) - (((count turtles-here + 1 - max_allee_size) ^ 2) / b) ;;to enable perfect knowledge, expected suitability establishes what an agent can expect to receive if they join any given patch
		]

end

to set-heterogeneity

  if Abundance = "Low Abundance" [
    if Heterogeneity = "Little Heterogeneity" [set add.prod 250]
    if Heterogeneity = "Some Heterogeneity" [set add.prod 1250]
    if Heterogeneity = "High Heterogeneity" [set add.prod 4250]
  ]

  if Abundance = "Mid Abundance" [
    if Heterogeneity = "Little Heterogeneity" [set add.prod 150]
    if Heterogeneity = "Some Heterogeneity" [set add.prod 550]
    if Heterogeneity = "High Heterogeneity" [set add.prod 2000]
  ]

  if Abundance = "High Abundance" [
    if Heterogeneity = "Little Heterogeneity" [set add.prod 100]
    if Heterogeneity = "Some Heterogeneity" [set add.prod 375]
    if Heterogeneity = "High Heterogeneity" [set add.prod 1250]
  ]

end

to color-patches
  ask patches [
    let mx max [productivity] of patches
    let mn min [productivity] of patches
    let normalized-value productivity / mx
    ifelse (Heterogeneity = "Homogeneous")
    [set pcolor yellow + 4]
    [set pcolor scale-color (yellow + 4) normalized-value 3 0];;scale color of patch by productivity: more productive patches are a darker color
  ]
end

to set-variable-combo
  ;;this is a submodel that sets a unique variable combination name for each possible parameter combination. This is used in the analysis to link iterations of the same parameter combinations.
  set variable-combo []
  if max_allee_size = 2 [set variable-combo lput "a" variable-combo]
  if max_allee_size = 5 [set variable-combo lput "b" variable-combo]
  if max_allee_size = 10 [set variable-combo lput "c" variable-combo]

  if population = "Low" [set variable-combo lput "d" variable-combo]
  if population = "Mid" [set variable-combo lput "e" variable-combo]
  if population = "High" [set variable-combo lput "f" variable-combo]

  if Heterogeneity = "Little Heterogeneity" [set variable-combo lput "g" variable-combo]
  if Heterogeneity = "More Heterogeneity" [set variable-combo lput "h" variable-combo]
  if Heterogeneity =  "Severe Heterogeneity" [set variable-combo lput "i" variable-combo]

  if Abundance = "Low Abundance" [set variable-combo lput "j" variable-combo]
  if Abundance = "Mid Abundance" [set variable-combo lput "k" variable-combo]
  if Abundance = "High Abundance" [set variable-combo lput "l" variable-combo]

  if Predictability = "Not_Predictable" [set variable-combo lput "m" variable-combo]
  if Predictability = "Somewhat_Predictable" [set variable-combo lput "n" variable-combo]
  if Predictability = "Completely_Predictable" [set variable-combo lput "o" variable-combo]

  if Defense.Cost = "Difficult_Defend" [set variable-combo lput "p" variable-combo]
  if Defense.Cost = "Somewhat_Defend" [set variable-combo lput "q" variable-combo]
  if Defense.Cost = "Easily_Defend" [set variable-combo lput "r" variable-combo]

end

to make-agents
  if Population = "Low" [set population_size 386]
  if Population = "Mid" [set population_size 876]
  if population = "High" [set population_size 2000]

  	ask patch 0 0 [sprout population_size;;all turtles are starting at the top left patch and the  patch has no productivity (so that turtles must move)
  ]
  ;;have turtles make themselves yellow and person shaped
	ask turtles [
		set shape "person"
    set band-size-list [];;create an empty list for the count of turtles they interact with each turn (band size)
    set resource-per-turn-list [];;create an empty list for the resources received each turn within a tick
    set avg-band-size 0
    set strategy one-of ["Free" "UA"];;assign each turtle one of the possible strategies   Deny is removed from this model run "Deny"
    set defender "n"
    set UA-role "NA"
    agent-color
	]
end

to agent-color
  if strategy = "Free" [set color (cyan + 3)]
  if strategy = "Deny" [set color (cyan - 1)]
  if strategy = "UA" [set color (blue + 1)]
  if UA-role != "NA" [
    ifelse UA-role = "Follower-Client"
      [set color (blue + 1)]
      [set color (violet - 1)]
  ]
end


to setup-reporters
  set turtles_per_turn []
  set patches_per_turn []
  set running-avg-group-size []
  set group-list []
  set final-turns-alive-list []
  set percent_moved_list []
  set proportion_UA []
  set proportion_Free []
  set num_moved 0
end

to set-defense-cost
  ;this is a world sub-model, that sets the cost of defense based
  set def.cost Defense.Cost
end
;;defense.cost is standardized on the mean patch. So, with a mean patch suitability of 1, a lone defender would pay 10 times the suitability if the defense cost is 10, meaning the suitability for them
;;would be -9. Doing this follows theory on the influence of defense cost and is separate from heterogeneity of resources in the environment. Heterogeneity is representing how homogeneously or heterogeneously
;;resources are distributed across all the patches in the environment. Defense.Cost is a within patch variable that can relate to things like how storable a resource is, if there are defendable
;;tools or production engingeering (for example, irrigation), or how densely clustered resources are within the patch and not just across the environment.


to set-predictability-probability
  if Predictability = "Not_Predictable" [set pred-prob 0]
  if Predictability = "Somewhat_Predictable" [set pred-prob 0.5]
  if Predictability = "Completely_Predictable" [set pred-prob 1]

end


to go

  reset-statuses

  set intra-turn 0

  while [intra-turn < 2]
  [;;if it is the first turn, all turtles move
    ifelse intra-turn = 0
    [
      ask turtles
       [
        find-patch
       ]
      calc-resources
      be-predictable
      color-patches ;;recolor patches to reflect the swapped changes
      plot-resources
      record-num-moved
      record-avg-group
      record-band-size
      record-med-group
    ]
    [;;else if it is the 2nd or 3rd turn, only Free Access turtles are able to move again
      ask turtles with [strategy = "Free"]
        [
          find-patch
        ]
      calc-resources
      be-predictable
      color-patches ;;recolor patches to reflect the swapped changes
      plot-resources
      record-num-moved
      record-avg-group
      record-band-size
      record-med-group
    ]
    set intra-turn intra-turn + 1
  ]

  compare-strategy
  ask turtles [agent-color];have the agents recolor after changing or not changing their strategy
  report-strat-changes
  tick
 ; if ticks = 200 [stop]

end

to reset-statuses
  ;this is an agent and patch sub-model to reset agent statuses that are dynamic on each tick
  ask turtles
    [
      set defender "n"
      set changed-strat "n"
      set UA-role "NA"
      set resource-per-turn-list [];;reset the resources to an empty list when you start a new tick
    ]
  ask patches
    [
      set last-turn-strat turtle-strat
      set defended 0
      set turtle-strat "NA"
    ]
end


to find-patch
  ;this is an agent sub-model leading agents to seek the patch granting them the best returns they can obtain.

      let options1 patches with [turtle-strat = "NA" or turtle-strat = [strategy] of myself];;only move to patches that have no set strategy or share your strategy
      let options options1 with [defended = 0] ;;perfect landscape knowledge – all patches that aren't actively defended are an option
      set target max-one-of options [exp_suit];; target the patch with the highest expected suitability (this is the suitability of the patch if you join it)

      if target = nobody [die];;if there is no place a particular agent can move (either no available patches or all patches employing their strategy are already defended)
      ;;the agent is removed from the landscape, emulating out-migration in response to lack of territory availability.

          ifelse [exp_suit] of target > [suitability] of patch-here ;;if the expected suitability of the target patch is > suitability of where you are
        ;;if code
            [
              attempt-move-to-target ;;call the attempt-move-to-target sub-model to determine if movement to target will happen or needs to reset due to defense
            ];;end if code

        ;;else code
            [;;else if the best target isn't better than where the turtle is at stay if can but must move if patch strat has changed
              check-if-remain ;;call the check-if-remain sub-model to determine if staying will happen or need to move because of a patch-strat change
            ]


end

to attempt-move-to-target
  ;this is an agent sub-model to determine if agents occupying a patch another agent wishes to move to will defend the patch or not

  ifelse not any? turtles-on target or [turtle-strat] of target = "NA"
    [ ;;if no other turtles are present, or the agent is the first to go/move, agent is free to move to target
      ask patch-here [calc-leave-suit] ;;have the patch you are leaving calculate a new expected suitability
      move-to target ;;move to the target patch
      set moves moves + 1
      set num_moved num_moved + 1;;add to the tally of turtles that have moved during the turn
      set time-in-place 1;;note that the turtle has been on the current patch for only 1 turn
      ifelse strategy = "UA"
        [;;if I am UA strategy and the first to a patch, I become Leader/Patron
          set UA-role "Leader-Patron"
          ask patch-here
            [
              set turtle-strat [strategy] of myself
              calc-UA-suit
            ];;calculate new expected suitabilities with a joining cost factored in
        ]
        [;;else if Deny or Free strategy
          ask patch-here
            [
              set turtle-strat [strategy] of myself ;;have the new patch record the strategy for this turn
              calc-new-suit
            ]
        ]
    ]

  [;;otherwise, if target is occupied or has a strategy already - check the strategy and act accordingly

  if [turtle-strat] of target = "Free"
     [
       ask patch-here [calc-leave-suit] ;;have the patch you are leaving calculate a new expected suitability
       move-to target
       set moves moves + 1
       set num_moved num_moved + 1;;add to the tally of turtles that have moved during the turn
       set time-in-place 1;;note that the turtle has been on the current patch for only 1 turn
       ask patch-here ;;ask new patch
         [
           calc-new-suit
         ]
     ]

  let occupiers turtles-on target ;;make a temporary agentset of the agents occupying the target patch

  ;;if there are any Deny turtles on the target patch, those turtles must decide if they are defending or not
  if [turtle-strat] of target = "Deny"
    [
      ask one-of occupiers with [strategy = "Deny"] ;;choose a representative Deny turtle
        [ifelse [exp_suit] of patch-here >= [suitability] of patch-here
          [] ;;if having another turtle join does not decrease returns, let the turtle join
          [defend] ;;else, if having another turtle join decreases returns, defend
        ]

      ;;after representative Deny turtle has chosen to defend or not, make move contingent on if the patch is defended
      ifelse [defended = 0] of target ;;if the target is not defended, move to it.
        [
          ask patch-here [calc-leave-suit]
          move-to target
          set moves moves + 1
          set num_moved num_moved + 1
          set time-in-place 1;;note that the turtle has been on the current patch for only 1 turn
          ask patch-here ;;ask the new patch
            [
              calc-new-suit
            ]
        ]
        [find-patch] ;;if the target is defended, re-enter the find-patch sub-model
    ]

  ;;if the patch turtle-strat is already set to UA, some turtle must have claimed it as Leader/Patron, so Leader/Patron decides if patch will be defended
    if [turtle-strat] of target = "UA"
    [
      ask one-of occupiers with [UA-role = "Leader-Patron"];;ask the Patron to evaluate if defense will happen
        [
          call-follower-client-defense ;;patron evaluates if adding another follower/client benefits them or not and either defends or doesn't
        ]

      ;;make move contingent on if the patch is defended
      ifelse [defended = 0] of target ;;if the target is not defended, move to it.
        [
          ask patch-here [calc-leave-suit]
          move-to target
          set moves moves + 1
          set num_moved num_moved + 1
          set time-in-place 1;;note that the turtle has been on the current patch for only 1 turn
          set UA-role "Follower-Client"
          ask patch-here
            [
              calc-UA-suit
            ]
        ]
        [find-patch] ;;else if the target is defended, re-enter the find-patch sub-model
    ]
  ];;end else code
end

to check-if-remain
  ;;this is an agent sub-model for evaluating if a turtle can remain on its current patch during its move phase of each tick

            ifelse [turtle-strat] of patch-here = "NA"
            [;;if I'm the first to elect to stay, I set the strategy
              ifelse strategy = "UA"
                [ ;;if I'm the first to stay and I use the UA strategy, I become Leader/Patron
                  set UA-role "Leader-Patron"
                  set time-in-place time-in-place + 1
                  ask patch-here
                    [
                      set turtle-strat [strategy] of myself
                      calc-UA-suit ;;this might need to be the suitability of the patch with only agents who are UA on it
                    ]
                ]
                [;;else if I'm the first to stay and I use Free or Deny
                  set time-in-place time-in-place + 1
                  ask patch-here
                    [
                      set turtle-strat [strategy] of myself
                      calc-new-suit;;this might need to be the suitability of the patch with only those of the same strategy on it. LOOK AT RECODING
                    ]
                ]
             ]

          [;;else if I'm not the first to stay
           if [turtle-strat] of patch-here = [strategy] of self
             [;;if I'm still playing the strategy of the patch, stay
               set time-in-place time-in-place + 1
               ifelse strategy = "UA"
                 [;;if I'm not the first UA agent to stay/be here, I become Follower/Client
                   set UA-role "Follower-Client"
                   ask patch-here [calc-UA-suit];;this might need to be the suitability of the patch with only agents who are UA on it
                 ]
                 [;;else if I am Deny or Free
                   ask patch-here [calc-new-suit];;this might need to be the suitability of the patch with only those of the same strategy on it. LOOK AT RECODING
                 ]
             ]

           if [turtle-strat] of patch-here != [strategy] of self
             [;;if I want to stay but the patch has changed strategies I must leave
               find-next-best
             ]
  ]
end

to calc-leave-suit
  ;this is a patch sub-model to calculate the suitability and expected suitability for agents on a patch that a current agent is leaving

  ifelse turtle-strat = "UA"
    [;if leaving a UA patch, calculate new expected suitability with the joining cost factored in
      set exp_suit (productivity / mean-patch-prod) - (((count turtles-here - max_allee_size) ^ 2) / b)
      set exp_suit (exp_suit - (exp_suit * c))
      set suitability (productivity / mean-patch-prod) - ((count turtles-here - 1 - max_allee_size) ^ 2 / b);;calculate new suitability with the effect of the joining cost imposed
      set suitability (suitability - (suitability * c))
    ]

    [;else code
      set exp_suit (productivity / mean-patch-prod) - (((count turtles-here - max_allee_size) ^ 2) / b) ;;calculate a new expected suitability
      set suitability (productivity / mean-patch-prod) - ((count turtles-here - 1 - max_allee_size) ^ 2 / b);;calculate new suitability for any remaining agents
    ]
end

to calc-new-suit
  ;this is a patch sub-model for generating new suitability and expected suitability when a turtle joins the patch

          set suitability exp_suit;;sets a new patch suitability value to be what the expected suitability was with 1 more turtle joining
          set exp_suit (productivity / mean-patch-prod) - (((count turtles-here + 1 - max_allee_size) ^ 2) / b);; calculate a new expected suitability

end

to calc-UA-suit
  ;this is a patch sub-model for generating suitability and expected suitability for patches controlled by UA turtles. This suitability and expected suit apply to followers/clients.

  set suitability (productivity / mean-patch-prod) - ((count turtles-here - max_allee_size) ^ 2 / b)
  set exp_suit_noc (productivity / mean-patch-prod) - ((((count turtles-here + 1) - max_allee_size) ^ 2) / b);;expected suit without join cost applied
  set exp_suit (exp_suit_noc - (exp_suit * c)) ;;apply the join cost. Any joining agent will receive 10% less than what would be expected if there were no leader/patron.

end


to defend
  ;this is an agent sub-model to determine if Deny agents successfully defend a patch or not

  ;as we are looking for what environmental conditions promote the emergence or suppression of unequal behaviors, agents who are Deny will always evaluate trying to defend
  ;the moment adding another turtle would lower their return - regardless of it is optimal in this precise moment. However, for defense to occur, the patch needs a number of
  ;defenders equal to the max_allee_size. If they don't have enough active defenders (due to free-riding) they cannot defend the patch.
  ask turtles-here with [strategy = "Deny" and defender = "n"] ;;representative turtle gathers all other Deny turtles on the patch who haven't yet determined if they are free-riding on this turn
    [
      let free-riding? precision random-float 1 2 ;; get a random number between 0 and 1, rounded to 2 decimal places
      ifelse free-riding? < prob-free-ride ;;if the random number is smaller than the probability of free-riding
        [set defender "f"];;free-ride
        [set defender "y"];;else if the random number is larger than the probability of free-riding, defend
    ]

  ask patch-here
    [
      ifelse count turtles-here with [defender = "y"] >= max_allee_size ;;if you have enough defenders to equal the max allee size
        [set defended 1];;the patch is defended
        [];; else if there aren't enough defenders, the patch cannot be defended yet
    ]

end

to call-follower-client-defense
  ;this is an agent sub-model for Leaders/Patrons to evaluate if they will be taking on another follower/client or defending the patch

  ;calculate the returns to Patron if the individual doesn't join and does join
  let suit_no_join (productivity / mean-patch-prod) - ((count turtles-here - max_allee_size) ^ 2 / b) + (((productivity / mean-patch-prod) - ((count turtles-here - max_allee_size) ^ 2 / b)) * c * (count turtles-here - 1))
  let suit_yes_join (productivity / mean-patch-prod) - ((count turtles-here + 1 - max_allee_size) ^ 2 / b) + (((productivity / mean-patch-prod) - ((count turtles-here + 1 - max_allee_size) ^ 2 / b)) * c * (count turtles-here))
  ;;we need (c* count turtles-here - 1) in the first part of the equation because leader must remove self from consideration. Leaders/patrons don't count as their own follower/client.
  ;;therefore the second half of the equation we do (c * count turtles-here) because not removing 1 emulates the effect of adding the new follower/client.
  ;;these equations calculate the amount of suitability added to a leader/patron's suitability from the follower/client turtles

  ;if the suitability of the patch + the benefit of followers/clients to leader/patron < suitability of the patch + benefit of follower/clients + 1 to leader/patron - allow new follower/client to join
  ifelse suit_no_join < suit_yes_join
    [];;don't defend
    [;;else, defend
      ask turtles-here with [strategy = "UA"]
        [
          set defender "y"
        ]

      ask patch-here
        [
          set defended 1
        ]
    ]

end

;;NEED TO MAKE SURE THIS WORKS FOR UA TURTLES AS WELL AS Free AND Deny
to find-next-best
  ;this is an agent sub-model for if agents cannot remain on their current patch
  let home-ycor [pycor] of patch-here
  let home-xcor [pxcor] of patch-here
  let options1 patches with [turtle-strat = "NA" or turtle-strat = [strategy] of myself];;only move to patches that have no set strategy or share your strategy
  let options options1 with [defended = 0] ;;perfect landscape knowledge – all patches that aren't actively defended are an option
  let options2 options with [pycor != home-ycor and pxcor != home-xcor];;remove your current patch from the options list
  set target max-one-of options2 [exp_suit];; target the patch with the highest expected suitability (this is the suitability of the patch if you join it)

  if target = nobody [die];;if there is no place a particular agent can move (either no available patches or all patches employing their strategy are already defended)
      ;;the agent is removed from the landscape, emulating out-migration in response to lack of territory availability.

    attempt-move-to-target

end


;;NEED TO CONFIRM THIS IS WORKING FOR UA TURTLES
to calc-resources
  ;this is an agent sub-model to calculate the resources each agent on a patch receives at the end of each turn

  ask turtles [;;free-access agents simply share the patch returns
     if strategy = "Free"
       [
         set resources precision [suitability] of patch-here 2 ;;have the turtle running this code set their resources to the patch suitability of the patch they are on
         set resource-per-turn-list lput resources resource-per-turn-list ;;add the new resources received to the list of resources received on each turn within the tick
       ]

     if strategy = "Deny" and defender = "n";;denial strategy agents who did not defend (no agent tried to join beyond max_allee_size so defense was never attempted) share patch returns
       [
         set resources precision [suitability] of patch-here 2 ;;have the turtle running this code set their resources to the patch suitability of the patch they are on
         set resource-per-turn-list lput resources resource-per-turn-list ;;add the new resources received to the list of resources received on each turn within the tick
       ]

     if strategy = "Deny" and defender = "f";;denial strategy agents who free-rode get patch returns without paying a defense cost
       [
         set resources precision [suitability] of patch-here 2 ;;have the turtle running this code set their resources to the patch suitability of the patch they are on
         set resource-per-turn-list lput resources resource-per-turn-list ;;add the new resources received to the list of resources received on each turn within the tick
       ]

     if strategy = "Deny" and defender = "y";;denial strategy agents who participated in defense split defense cost and take that away from their returns
       [
         set resources precision ([suitability] of patch-here - ((1 * def.cost) / count turtles-here with [defender = "y"])) 2 ;;defending agents receive patch returns but pay a defense cost.
         set resource-per-turn-list lput resources resource-per-turn-list ;;add the new resources received to the list of resources received on each turn within the tick
       ] ;;defense cost is standardized off of the mean patch suitability. Mean patch suit is 1, given mean productivity is 3300. Patches with > 3300 resources represent > benefit
;; to defense - simulating greater clumping of resources. precision ..... 2 means to round the value to 2 decimal places. While the 1 in (1 * def.cost) is unnecessary mathematically at the moment,
    ;;it is left in to represent that def.cost is relative to the mean patch. If mean patch is changed so the mean isn't a suitability of 1, this value must be changed too.

     if strategy = "UA" and defender = "n";;UA strategy agents who did not have to defend share patch returns with kickback factored in
       [
         ifelse UA-role = "Leader-Patron"
           [;;if Leader/Patron
             set resources precision ([suitability] of patch-here + ([suitability] of patch-here * c * (count turtles-here - 1))) 2
             set resource-per-turn-list lput resources resource-per-turn-list ;;add the new resources received to the list of resources received on each turn within the tick
           ]

           [;;else if Follower/Client
             set resources precision ([suitability] of patch-here - ([suitability] of patch-here * c)) 2
             set resource-per-turn-list lput resources resource-per-turn-list ;;add the new resources received to the list of resources received on each turn within the tick
           ]
       ]

     if strategy = "UA" and defender = "y";;UA strategy agents who defended share patch returns with kickback factored in and split defense cost
       [
         ifelse UA-role = "Leader-Patron"
           [;;if Leader/Patron
             set resources precision (([suitability] of patch-here + ([suitability] of patch-here * c * (count turtles-here - 1))) - ((1 * def.cost) / count turtles-here)) 2
             set resource-per-turn-list lput resources resource-per-turn-list ;;add the new resources received to the list of resources received on each turn within the tick
           ]
           [;;else if Follower/Client
          set resources precision (([suitability] of patch-here - ([suitability] of patch-here * c)) - ((1 * def.cost) / count turtles-here)) 2
          set resource-per-turn-list lput resources resource-per-turn-list ;;add the new resources received to the list of resources received on each turn within the tick
           ]
       ]
  ]


end

to plot-resources
  set-current-plot "Avg Resources by Strategy"
    set-current-plot-pen "Free"
      ifelse count turtles with [strategy = "Free"] >= 1
        [plot (sum [resources] of turtles with [strategy = "Free"]) / count turtles with [strategy = "Free"]]
        []
;    set-current-plot-pen "Deny"
;      ifelse count turtles with [strategy = "Deny"] >= 1
;        [plot (sum [resources] of turtles with [strategy = "Deny"]) / count turtles with [strategy = "Deny"] ]
;        []
    set-current-plot-pen "Follower-Client"
       ifelse count turtles with [UA-role = "Follower-Client"] >= 1
          [plot (sum [resources] of turtles with [UA-role = "Follower-Client"]) / count turtles with [UA-role = "Follower-Client"] ]
          []
    set-current-plot-pen "Leader-Patron"
       ifelse count turtles with [UA-role = "Leader-Patron"] >= 1
          [plot (sum [resources] of turtles with [UA-role = "Leader-Patron"]) / count turtles with [UA-role = "Leader-Patron"] ]
          []


  set-current-plot "Max Resources by Strategy"
    set-current-plot-pen "Free"
      ifelse count turtles with [strategy = "Free"] >= 1
        [plot max [resources] of turtles with [strategy = "Free"]]
        []
;    set-current-plot-pen "Deny"
;      ifelse count turtles with [strategy = "Deny"] >= 1
;        [plot max [resources] of turtles with [strategy = "Deny"]]
;        []
    set-current-plot-pen "Follower-Client"
       ifelse count turtles with [UA-role = "Follower-Client"] >= 1
          [plot max [resources] of turtles with [UA-role = "Follower-Client"]]
          []
    set-current-plot-pen "Leader-Patron"
       ifelse count turtles with [UA-role = "Leader-Patron"] >= 1
          [plot max [resources] of turtles with [UA-role = "Leader-Patron"]]
          []

end


to compare-strategy
  ;this is an agent sub-model that has each agent compare the returns from its strategy this turn with another agent at random
;if ticks >= 1 [
  ask turtles [
    let comparison one-of other turtles
    let my-returns (sum resource-per-turn-list / intra-turn)
    let comparison-returns (sum [resource-per-turn-list] of comparison / intra-turn)

    if comparison-returns > my-returns
      [;if the agent you are comparing yourself with did better than you, use their strategy next turn
        if [strategy] of comparison != strategy
          [
            set strategy [strategy] of comparison
            set changed-strat "y"
          ]
      ]
  ]
;  ]
end

to report-strat-changes
  ;this is a reporter for the percent of turtles changing strategy each turn
  let total-changed count turtles with [changed-strat = "y"]
  set perc-changed-on-turn total-changed / count turtles

  ;we will also record the percent agents playing each strategy at the end of each turn
  set proportion_UA lput (count turtles with [strategy = "UA"] / count turtles) proportion_UA
  set proportion_Free lput (count turtles with [strategy = "Free"] / count turtles) proportion_Free

end


to record-band-size

  ask patches [set num_turts count turtles-here];;grab a count of the number of turtles on each patch

  ask turtles [
    set band-size-list lput count turtles-here band-size-list;; keep a list of the band sizes experienced by each turtle on each turn. Band includes self.
    set avg-band-size (sum band-size-list / (ticks + 1)) ;;generate an individual turtle's avg experienced band size
  ]

end


to record-num-moved
if ticks > 0 [;;don't record the movement on the first turn, only subsequent turns since all agents are forced to move on turn 1.
let percent_moved (num_moved / count turtles)
set percent_moved_list lput percent_moved percent_moved_list
  ]
set num_moved 0
if ticks > 0 [;;only do after first turn
    set avg_percent_moved (sum percent_moved_list / (ticks + 1));;record the number moved at each tick
  ]
end


to record-avg-group
    let tick-avg-group-size count turtles / (count patches with [any? turtles-here]) ;;average group size is the total turtles divided by the number of patches that have turtles on them
    set running-avg-group-size lput tick-avg-group-size running-avg-group-size ;;make a list of each tick's average group size
    set avg-group-size sum running-avg-group-size / ((ticks + 1) * 2) ;;generate the full model run average group size by taking each tick's average group size and dividing by the total number of ticks. Multiply
    ;;ticks by 2 because there are two turns being recorded per tick. So we get two group size estimates per tick (turn 1 and turn 2).
end

to record-med-group
    let tick-group-list [];;make an empty list for the group size on each tick
    ask patches with [any? turtles-here] [set tick-group-list lput count turtles-here tick-group-list];;generate a list that is the number of turtles on each of the occupied patches
    let tick-med-group-size median tick-group-list
    set group-list lput tick-med-group-size group-list ;;add the tick median group size to a list of median group sizes from every tick
    set med-group-size median group-list;; get the median from the list (this is the median group size of each tick's median group size)
end

to be-predictable
    ask patches [
      let change random-float 1
      if change > pred-prob [ ;;somewhat predictable is implying there is a 50:50 chance the resource remains in a known location. But I don't want predictability to change the total productivity in the world. So I need to allow unpredictable patches to swap
        ;;their productivity with another unpredictable patch. If I do a swap I should be keeping the total heterogeneity the same.
      set unpredictable 1
      ]
    ]

  if count patches with [unpredictable = 1] > 2 [
     exchange-productivity ;;run a procedure to have unpredictable patches swap productivity with each other
  ]

  ask patches[
  ;calculate the suitability and exp_suit for the first person to move the next turn
        set suitability (productivity / mean-patch-prod) - (((count turtles-here - max_allee_size) ^ 2) / b) ;;set suitability to be the returns a turtle would get as the first turtle on a patch. Standardized on mean patch of 3300.
        set exp_suit (productivity / mean-patch-prod) - (((count turtles-here + 1 - max_allee_size) ^ 2) / b) ;;to enable perfect knowledge, expected suitability establishes what an agent can expect to receive if they join any given patch
  ]


end

to exchange-productivity
  while [count patches with [unpredictable = 1] >= 2] [
  ask one-of patches with [unpredictable = 1] [
    let swap-prod productivity
  ask one-of patches with [unpredictable = 1] [
    set swap-patch 1
    set return-prod productivity
    set productivity swap-prod
    set unpredictable 0
  ]
    set productivity [return-prod] of one-of patches with [swap-patch = 1]
    set unpredictable 0
    ask patches with [swap-patch = 1] [set swap-patch 0]
]
  ]

end
@#$#@#$#@
GRAPHICS-WINDOW
295
55
803
564
-1
-1
50.0
1
10
1
1
1
0
1
1
1
0
9
-9
0
0
0
1
ticks
60.0

BUTTON
155
105
220
138
Go
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
840
105
1005
150
# Turtles on Occupied Patches
count turtles / (count patches with [any? turtles-here])
2
1
11

MONITOR
1050
50
1165
95
NIL
avg_percent_moved
2
1
11

MONITOR
1125
160
1222
205
Avg Group Size
avg-group-size
2
1
11

PLOT
840
395
1110
585
No. Turtles per Occupied Patch
Number of Turtles
Count of Patches
0.0
30.0
0.0
50.0
true
false
"" ""
PENS
"default" 1.0 1 -16777216 true "" "histogram [num_turts] of patches with [any? turtles-here]"

CHOOSER
65
300
232
345
Heterogeneity
Heterogeneity
"Little Heterogeneity" "Some Heterogeneity" "High Heterogeneity"
1

BUTTON
85
105
147
138
NIL
setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

CHOOSER
65
350
242
395
Predictability
Predictability
"Not_Predictable" "Somewhat_Predictable" "Completely_Predictable"
2

MONITOR
840
160
995
205
% Changing Strategy on Turn
perc-changed-on-turn
2
1
11

PLOT
1120
395
1390
585
Turtles by Strategy
NIL
NIL
0.0
10.0
0.0
1.0
true
true
"" ""
PENS
"Free" 1.0 0 -4528153 true "" "plot (count turtles with [strategy = \"Free\"]) / count turtles"
"Unequal" 1.0 0 -10141563 true "" "plot (count turtles with [strategy = \"UA\"]) / count turtles"
"Deny" 1.0 0 -12345184 true "" "plot (count turtles with [strategy = \"Deny\"]) / count turtles"

PLOT
840
210
1110
390
Avg Resources by Strategy
NIL
NIL
0.0
10.0
0.0
2.0
true
true
"" ""
PENS
"Free" 1.0 0 -4528153 true "" ""
"Follower-Client" 1.0 0 -10649926 true "" ""
"Leader-Patron" 1.0 0 -10141563 true "" ""
"Deny" 1.0 0 -12345184 true "" ""

MONITOR
1010
105
1110
150
Mean Productivity
sum [productivity] of patches / count patches
2
1
11

MONITOR
840
50
937
95
% Turtles Alive
count turtles / population_size
2
1
11

MONITOR
945
50
1042
95
# Living Turtles
count turtles
17
1
11

CHOOSER
65
250
262
295
Abundance
Abundance
"Low Abundance" "Mid Abundance" "High Abundance"
1

PLOT
1120
210
1390
390
Max Resources by Strategy
NIL
NIL
0.0
10.0
0.0
2.0
true
true
"" ""
PENS
"Free" 1.0 0 -4528153 true "" ""
"Follower-Client" 1.0 0 -10649926 true "" ""
"Leader-Patron" 1.0 0 -10141563 true "" ""
"Deny" 1.0 0 -12345184 true "" ""

MONITOR
1005
160
1117
205
Median Group Size
med-group-size
2
1
11

MONITOR
1115
105
1242
150
St. Dev. Productivity
standard-deviation [productivity] of patches
2
1
11

CHOOSER
65
150
203
195
Population
Population
"Low" "Mid" "High"
1

CHOOSER
65
200
203
245
Allee-Effect
Allee-Effect
"Small" "Medium" "Large"
1

SLIDER
65
440
237
473
Leader-Patron_Cost
Leader-Patron_Cost
0
0.5
0.1
0.05
1
NIL
HORIZONTAL

SLIDER
65
400
237
433
prob-free-ride
prob-free-ride
0
1
0.5
0.05
1
NIL
HORIZONTAL

SLIDER
65
480
237
513
Defense.Cost
Defense.Cost
1
15
9.0
2
1
NIL
HORIZONTAL

@#$#@#$#@
## WHAT IS IT?

(a general understanding of what the model is trying to show or explain)

## HOW IT WORKS

(what rules the agents use to create the overall behavior of the model)

## HOW TO USE IT

(how to use the model, including a description of each of the items in the Interface tab)

## THINGS TO NOTICE

(suggested things for the user to notice while running the model)

## THINGS TO TRY

(suggested things for the user to try to do (move sliders, switches, etc.) with the model)

## EXTENDING THE MODEL

(suggested things to add or change in the Code tab to make the model more complicated, detailed, accurate, etc.)

## NETLOGO FEATURES

(interesting or unusual features of NetLogo that the model uses, particularly in the Code tab; or where workarounds were needed for missing features)

## RELATED MODELS

(models in the NetLogo Models Library and elsewhere which are of related interest)

## CREDITS AND REFERENCES

(a reference to the model's URL on the web if it has one, as well as any other necessary credits, citations, and links)
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.1.1
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
<experiments>
  <experiment name="25_reps_1def" repetitions="25" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Little Heterogeneity&quot;"/>
      <value value="&quot;Some Heterogeneity&quot;"/>
      <value value="&quot;High Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Not_Predictable&quot;"/>
      <value value="&quot;Somewhat_Predictable&quot;"/>
      <value value="&quot;Completely_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Low Abundance&quot;"/>
      <value value="&quot;Mid Abundance&quot;"/>
      <value value="&quot;High Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Small&quot;"/>
      <value value="&quot;Medium&quot;"/>
      <value value="&quot;Large&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="1"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="25_reps_3def" repetitions="25" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Little Heterogeneity&quot;"/>
      <value value="&quot;Some Heterogeneity&quot;"/>
      <value value="&quot;High Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Not_Predictable&quot;"/>
      <value value="&quot;Somewhat_Predictable&quot;"/>
      <value value="&quot;Completely_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Low Abundance&quot;"/>
      <value value="&quot;Mid Abundance&quot;"/>
      <value value="&quot;High Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Small&quot;"/>
      <value value="&quot;Medium&quot;"/>
      <value value="&quot;Large&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="3"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="25_reps_5def" repetitions="25" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Little Heterogeneity&quot;"/>
      <value value="&quot;Some Heterogeneity&quot;"/>
      <value value="&quot;High Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Not_Predictable&quot;"/>
      <value value="&quot;Somewhat_Predictable&quot;"/>
      <value value="&quot;Completely_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Low Abundance&quot;"/>
      <value value="&quot;Mid Abundance&quot;"/>
      <value value="&quot;High Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Small&quot;"/>
      <value value="&quot;Medium&quot;"/>
      <value value="&quot;Large&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="5"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="25_reps_7def" repetitions="25" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Little Heterogeneity&quot;"/>
      <value value="&quot;Some Heterogeneity&quot;"/>
      <value value="&quot;High Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Not_Predictable&quot;"/>
      <value value="&quot;Somewhat_Predictable&quot;"/>
      <value value="&quot;Completely_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Low Abundance&quot;"/>
      <value value="&quot;Mid Abundance&quot;"/>
      <value value="&quot;High Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Small&quot;"/>
      <value value="&quot;Medium&quot;"/>
      <value value="&quot;Large&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="7"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="25_reps_9def" repetitions="25" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Little Heterogeneity&quot;"/>
      <value value="&quot;Some Heterogeneity&quot;"/>
      <value value="&quot;High Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Not_Predictable&quot;"/>
      <value value="&quot;Somewhat_Predictable&quot;"/>
      <value value="&quot;Completely_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Low Abundance&quot;"/>
      <value value="&quot;Mid Abundance&quot;"/>
      <value value="&quot;High Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Small&quot;"/>
      <value value="&quot;Medium&quot;"/>
      <value value="&quot;Large&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="9"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="25_reps_11def" repetitions="25" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Little Heterogeneity&quot;"/>
      <value value="&quot;Some Heterogeneity&quot;"/>
      <value value="&quot;High Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Not_Predictable&quot;"/>
      <value value="&quot;Somewhat_Predictable&quot;"/>
      <value value="&quot;Completely_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Low Abundance&quot;"/>
      <value value="&quot;Mid Abundance&quot;"/>
      <value value="&quot;High Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Small&quot;"/>
      <value value="&quot;Medium&quot;"/>
      <value value="&quot;Large&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="11"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="25_reps_13def" repetitions="25" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Little Heterogeneity&quot;"/>
      <value value="&quot;Some Heterogeneity&quot;"/>
      <value value="&quot;High Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Not_Predictable&quot;"/>
      <value value="&quot;Somewhat_Predictable&quot;"/>
      <value value="&quot;Completely_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Low Abundance&quot;"/>
      <value value="&quot;Mid Abundance&quot;"/>
      <value value="&quot;High Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Small&quot;"/>
      <value value="&quot;Medium&quot;"/>
      <value value="&quot;Large&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="13"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="25_reps_15def" repetitions="25" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Little Heterogeneity&quot;"/>
      <value value="&quot;Some Heterogeneity&quot;"/>
      <value value="&quot;High Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Not_Predictable&quot;"/>
      <value value="&quot;Somewhat_Predictable&quot;"/>
      <value value="&quot;Completely_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Low Abundance&quot;"/>
      <value value="&quot;Mid Abundance&quot;"/>
      <value value="&quot;High Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Small&quot;"/>
      <value value="&quot;Medium&quot;"/>
      <value value="&quot;Large&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="15"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="25_reps_01def" repetitions="25" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Little Heterogeneity&quot;"/>
      <value value="&quot;Some Heterogeneity&quot;"/>
      <value value="&quot;High Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Not_Predictable&quot;"/>
      <value value="&quot;Somewhat_Predictable&quot;"/>
      <value value="&quot;Completely_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Low Abundance&quot;"/>
      <value value="&quot;Mid Abundance&quot;"/>
      <value value="&quot;High Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Small&quot;"/>
      <value value="&quot;Medium&quot;"/>
      <value value="&quot;Large&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="0.1"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="25_reps_all_combos" repetitions="25" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Little Heterogeneity&quot;"/>
      <value value="&quot;Some Heterogeneity&quot;"/>
      <value value="&quot;High Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Not_Predictable&quot;"/>
      <value value="&quot;Somewhat_Predictable&quot;"/>
      <value value="&quot;Completely_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Low Abundance&quot;"/>
      <value value="&quot;Mid Abundance&quot;"/>
      <value value="&quot;High Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Small&quot;"/>
      <value value="&quot;Medium&quot;"/>
      <value value="&quot;Large&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="3"/>
      <value value="7"/>
      <value value="11"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="50_reps_LPcost_sensitivity" repetitions="50" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Some Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Somewhat_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Mid Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Medium&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="7"/>
    </enumeratedValueSet>
    <steppedValueSet variable="Leader-Patron_Cost" first="0.01" step="0.01" last="0.2"/>
  </experiment>
  <experiment name="100_reps_Defcost_sensitivity" repetitions="100" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="200"/>
    <metric>(count turtles with [strategy = "Free"] / count turtles)</metric>
    <metric>(count turtles with [strategy = "UA"] / count turtles)</metric>
    <metric>variable-combo</metric>
    <metric>population_size</metric>
    <metric>count turtles</metric>
    <metric>(count turtles / population_size)</metric>
    <metric>mean proportion_UA</metric>
    <metric>mean proportion_Free</metric>
    <enumeratedValueSet variable="Population">
      <value value="&quot;Mid&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Heterogeneity">
      <value value="&quot;Some Heterogeneity&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Predictability">
      <value value="&quot;Somewhat_Predictable&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Abundance">
      <value value="&quot;Mid Abundance&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Allee-Effect">
      <value value="&quot;Medium&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="Defense.Cost">
      <value value="0.1"/>
      <value value="1"/>
      <value value="2"/>
      <value value="3"/>
      <value value="4"/>
      <value value="5"/>
      <value value="6"/>
      <value value="7"/>
      <value value="8"/>
      <value value="9"/>
      <value value="10"/>
      <value value="11"/>
      <value value="12"/>
      <value value="13"/>
      <value value="14"/>
      <value value="15"/>
    </enumeratedValueSet>
  </experiment>
</experiments>
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
1
@#$#@#$#@
