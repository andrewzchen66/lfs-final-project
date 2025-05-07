#lang forge/temporal

option max_tracelength 12
option min_tracelength 12

---------- Definitions ----------

abstract sig GWPosition {
    var gw: set GWAnimal
}
one sig GWNear extends GWPosition {}
one sig GWFar extends GWPosition {}

abstract sig GWAnimal {}
sig Goat extends GWAnimal {}
sig Wolf extends GWAnimal {}

one sig GWBoat {
    var gwlocation: one GWPosition
}

pred GWvalidState {
    // TODO: Fill me in!

    // For this problem, valid states are ones 
    // which are physically reasonable:
    // - animals should be on one side or the other.
    // - the boat should be on one side or the other. 

    all animal: GWAnimal | {
        (animal in GWNear.gw and animal not in GWFar.gw) or (animal in GWFar.gw and animal not in GWNear.gw)
    }
    (GWBoat.gwlocation = GWNear or GWBoat.gwlocation = GWFar)
}

// Each of the predicates below should *assume* valid states
// but should *not enforce* valid states.

pred GWinitState {
    // TODO: Fill me in!
    // All of the animals and the boat should start on the near side
    all animal: GWAnimal | {
        animal in GWNear.gw
    }
    GWBoat.gwlocation = GWNear
}

pred GWfinalState {
    // TODO: Fill me in!
    // We want to see all of the animals reach the far side.
    all animal: GWAnimal | {
        animal in GWFar.gw
    }
    GWBoat.gwlocation = GWFar
}

pred GWmove[to, from: GWPosition] {
    // TODO: Fill me in!
    // The boat can carry at most two animals each way,
    // but it can't travel across the river on its own.
    // In particular:
    //  - the boat must move
    //  - exactly 1 or 2 animals cross with the boat 
    //  - every other animal stays in place

    // The boat must move
    GWBoat.gwlocation = from
    GWBoat.gwlocation' = to

    // exactly 1 or 2 animals cross with the boat, every other animal stays in place 
    from.gw' in from.gw and
    to.gw in to.gw' and
    (#{from.gw - from.gw'} = 1 or #{from.gw - from.gw'} = 2) and
    from.gw - from.gw' = to.gw' - to.gw
}

-----------------------------------------

pred GWneverEating {
    // TODO: Fill me in!
    // If the sheep are out numbered on one of the sides,
    // then the wolves can overpower and eat them!
    // Check to see if we can avoid that.
    
    // If Goats are present, then wolves shouldn't outnumber them
    (#GWNear.gw & Goat = 0 or #GWNear.gw & Goat >= #GWNear.gw & Wolf)
    (#GWFar.gw & Goat = 0 or #GWFar.gw & Goat >= #GWFar.gw & Wolf)
}

pred GWtraces { 
    // TODO: Fill me in!
    GWinitState
    always {
        GWvalidState
        GWneverEating
        GWmove[GWFar, GWNear] or GWmove[GWNear, GWFar]
    }
    eventually GWfinalState
}

run {
    GWtraces
} for exactly 6 GWAnimal, exactly 3 Goat, exactly 3 Wolf

// FOR AFTER YOU FINISH:

// What happens if you change "{min, max}_tracelength" to "11"? 
// Are there any shorter solutions?
// Write down your findings!

// ANSWER: After changing "{min, max}_tracelength" to "11", I got UNSAT.
// This implies that there are no shorter solutions than 12.

