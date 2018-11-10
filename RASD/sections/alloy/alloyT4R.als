open util/time

/* Users
***************************************************************************************************************************************/
abstract sig User{
	id: one Int
}
abstract sig ThirdPartyUser extends User{}
abstract sig IndividualUser extends User{
	info: one Info
}
sig Info{}

sig Organizer extends ThirdPartyUser{}

sig Participant extends IndividualUser{}
sig Spectator extends IndividualUser{}

sig Run{
	organizer: one Organizer,
	stateSet: RunState one -> Time, //state of the run for every instant in the time frame considered
	//Users who spectated the run
	spectatorSet: set Spectator,
	//Users who are participants at the end of the time frame considered
	participantSet: set Participant,
	//These two set represent the number of participants and spactators for every instant in the time frame considered
	participantNum: set Int one -> Time,
	spectatorNum: set Int one -> Time,
	restrictionSet: set Info //restriction are modeled as a set of not allowed info
}{
	all t: Time | one i: Int | participantNum.t = i
	all t: Time | one i: Int | spectatorNum.t = i
	//at the end of the time frame the number of participant is equal to participantNum
	all t: Time | (no t0: Time | gt[t0, t]) =>  participantNum.t = #(participantSet)
}
enum RunState{N, O, S, E, C}
//NOT_CREATED, ORGANIZED, STARTED, ENDED, CANCELD

/* Unicity facts
***************************************************************************************************************************************/
fact idUnique{
	no disjoint u1, u2: User | u1.id = u2.id
}

/* Run states facts
***************************************************************************************************************************************/
fact runStates{
	//A state is defined for every time istant after callTime
	all r: Run | all t: Time | one state: RunState |
		 state in r.stateSet.t
	//A run must have been in the "Non created" state at least once
	all r: Run | some t: Time | r.stateSet.t = N
	//When the run is "Not created" yet, it has never changed state	
	all r: Run | all t1, t2: Time | 
		(gte[t2, t1] && r.stateSet.t2 = N) => (r.stateSet.t1 = N)
	//If "Organized" has always been N or O
	all r: Run | all t1, t2: Time | 
		(gte[t2, t1] && r.stateSet.t2 = O) => (r.stateSet.t1 = N || r.stateSet.t1 = O)
	//If "Started" will "End"
	all r: Run | all t1, t2: Time | 
		(gte[t2, t1] && r.stateSet.t1 = S) => (r.stateSet.t1 = S || r.stateSet.t1 = E)
	//Once the run is "Ended" it can't change state again
	all r: Run | all t1, t2: Time | 
		(gte[t2, t1] && r.stateSet.t1 = E) => (r.stateSet.t2 = E)
	//If "Canceled" has never "Started"
	all r: Run | all t1, t2: Time | 
		(gte[t2, t1] && r.stateSet.t2 = C) => (not r.stateSet.t1 = S)
	//Once the run is "Canceled" it can't change state again
	 all r: Run | all t1, t2: Time | 
		(gte[t2, t1] && r.stateSet.t1 = C) => (r.stateSet.t2 = C)
	
}//Allowed state sequences: {N -> O -> S -> E}{N -> O -> C}


/* Joining facts
***************************************************************************************************************************************/
fact openEnroll{
	//If run is not in the "Organize" state none can enroll
	all r: Run | all t1, t2: Time | 
	(not(r.stateSet.t1 = N) && not (r.stateSet.t1 = O) && not(r.stateSet.t2 = N) && not (r.stateSet.t2 = O)) 
	=> 
	(r.participantNum.t1 = r.participantNum.t2)

	//If run is in the "Not Started" nobody enorlled
	all r: Run | all t: Time | 
	(r.stateSet.t = N)
	=> 
	(r.participantNum.t = 0)

	//If run is in not in the "Started" nobody is spectating
	all r: Run | all t: Time | 
	(not (r.stateSet.t = S))
	=> 
	(r.spectatorNum.t = 0)
}

/* Run state pred
***************************************************************************************************************************************/
pred organize[o: Organizer, t: Time]{
	one r: Run | 
		(r.stateSet.t = N) &&
		(r.organizer = o) &&

		(r.stateSet.(t.next) = O) &&
		(r.participantNum.(t.next) = 0) &&
		(r.spectatorNum.(t.next) = 0)
}

pred start[r: Run, t: Time]{
	//pre-conditions
	(r.stateSet.t = O)
	//post-conditions
	(r.stateSet.(t.next) = S)
}

pred end[r: Run, t: Time]{
	//pre-conditions
	(r.stateSet.t = S)
	//post-conditions
	(r.stateSet.(t.next) = E)
}

pred cancel[r: Run, t: Time]{
	//pre-conditions
	(r.stateSet.t = O)
	//post-conditions
	(r.stateSet.(t.next) = C) &&
	(r.spectatorNum.(t.next) = 0)
}

/* Enroll Run pred
***************************************************************************************************************************************/
pred enroll[p: Participant, r: Run, t: Time]{
	not (p.info in r.restrictionSet)
	r.participantNum.(t.next) = r.participantNum.t + 1
	p in r.participantSet
}

pred spectate[s: Spectator, r: Run, t: Time]{
	r.spectatorNum.(t.next) = r.spectatorNum.t + 1
	s in r.spectatorSet
}

/* Show
***************************************************************************************************************************************/
pred show{
 	#(ThirdPartyUser) = 1
	#(IndividualUser) = 2
	#(Info) = 3
	#(Run) = 2
	(some o: Organizer | some t: Time | organize[o, t])
	(some r: Run | some t: Time | start[r, t])
	(some r: Run | some t: Time | end[r, t])
	(some r: Run | some t: Time | cancel[r, t])
	(some r: Run | some t: Time | some p: Participant | enroll[p, r, t])
	(some r: Run | some t: Time | some s: Spectator | spectate[s, r, t])
}


/* Run
***************************************************************************************************************************************/
run organize for 5
run start for 5
run end for 5
run cancel for 5

run show for 5
