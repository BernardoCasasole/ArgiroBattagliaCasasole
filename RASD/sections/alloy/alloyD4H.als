open util/time

/*
The requests contain the set of state they were in the time frame considered.
The blocked TPUs are fixed and never change in the time frame.
The data accessible from the TPUs is the data is has access to after the time frame.
*/

/* Users
***************************************************************************************************************************************/
abstract sig User{
	id: one Int
}
sig ThirdPartyUser extends User{
	accessibleData: set Data	//The data accessible from the TPUs is the data is has access to after the time frame.
}
sig IndividualUser extends User{
	blockedTPUs: set ThirdPartyUser //The data accessible from the TPUs is the data is has access to after the time frame.
}	
sig Data{
	user: one IndividualUser,
	time: one Time
}

/* Request
***************************************************************************************************************************************/
abstract sig DataRequest{
	thirdPartyUser: one ThirdPartyUser,
	individualUser: one IndividualUser,
	stateSet: set RequestState -> Time //The requests contain the set of state they were in the time frame considered.
}
sig StoredDataRequest extends DataRequest{}
sig SubscriptionRequest extends DataRequest{}

enum RequestState{W, A, D}
//WAITING, APPROVED, DENYED
/*
sig RaceOrganizer extends ThirdPartyUser{}
sig RaceParticipant extends IndividualUser{}
sig RaceSpectator extends IndividualUser{}
*/


/* Unicity facts
***************************************************************************************************************************************/
fact idUnique{
	no disjoint u1, u2: User | u1.id = u2.id
}

/*Data requests cycle facts
***************************************************************************************************************************************/
fact dataRequestState{
	//A state is defined for every time istant
	all dr: DataRequest | all t: Time | one state: RequestState |
		 state in dr.stateSet.t
	//Created in "Waiting"
	all dr: DataRequest | all t: Time | some t0: Time | 
		gte[t, t0] && dr.stateSet.t0 = W
	//When the request is "Waiting", it has never changed state
	all dr: DataRequest | all t1, t2: Time | 
		(gte[t2, t1] && dr.stateSet.t2 = W) => (dr.stateSet.t1 = W)
	//Once the request is "Denyed" it can't change state again
	all dr: DataRequest | all t1, t2: Time | 
		(gte[t2, t1] && dr.stateSet.t1 = D) => (dr.stateSet.t2 = D)
}//Allowed state sequences: {W -> D}{W -> A}{W -> A -> D}

fact storedDataRequest{
	//Once the request is "Accepted" it can't change state again
	all sdr: StoredDataRequest | all t1, t2: Time | 
		(gte[t2, t1] && sdr.stateSet.t1 = A) => (sdr.stateSet.t2 = A)
}//Restricted allowed state sequences to: {W -> D}{W -> A}

/*Data access facts
***************************************************************************************************************************************/
fact accessibleData{
	all tpu: ThirdPartyUser | all data: Data |
		//Data regarding time t is accessible if
		(data in tpu.accessibleData) <=> 
		//exist a stored data request approved after time t
		((some sdr: StoredDataRequest | some t: Time |
			(sdr.individualUser = data.user) && 
			(sdr.thirdPartyUser = tpu) &&
			(sdr.stateSet.t = A) &&
			(sdr.stateSet.(data.time) = W)
			)
		||
		//exist a subscription request approved at time t
		((some sr: SubscriptionRequest |
			(sr.individualUser = data.user) && 
			(sr.thirdPartyUser = tpu) &&
			(sr.stateSet.(data.time) = A)
			)
		))
}

//For each individual user all data exists
fact completeData{
	all us: IndividualUser | all t: Time | one data: Data | data.user = us && data.time = t
}

/*Data request cycle pred
***************************************************************************************************************************************/
pred makeRequest[iu: IndividualUser, tpu: ThirdPartyUser, t: Time]{
	//pre-conditions
	not isBlocked[iu, tpu]
	//post-conditions
	one dr: DataRequest | dr.thirdPartyUser = tpu && dr.individualUser = iu && dr.stateSet.(t.next) = W
}
pred isBlocked[iu: IndividualUser, tpu: ThirdPartyUser]{
	tpu in iu.blockedTPUs
}
pred approveDataRequest[tpu: ThirdPartyUser, dr: DataRequest, t: Time]{
	//pre-conditions
	dr.stateSet.t = W
	//post-conditions
	dr.stateSet.(t.next) = A
}
pred denyStoredDataRequest[tpu: ThirdPartyUser, sdr: StoredDataRequest, t: Time]{
	//pre-conditions
	sdr.stateSet.t = W
	//post-conditions
	sdr.stateSet.(t.next) = D
}
pred denySubscriptionApproval[tpu: ThirdPartyUser, sr: SubscriptionRequest, t: Time]{
	//pre-conditions
	not sr.stateSet.t = D
	//post-conditions
	sr.stateSet.(t.next) = D
}

pred show{
 	#(ThirdPartyUser) = 1
	#(IndividualUser) = 1
	#(StoredDataRequest) = 1
	#(SubscriptionRequest) = 1
	//At least one tpu has access to some data
	(some tpu: ThirdPartyUser | #(tpu.accessibleData) > 0)
	(some iu: IndividualUser | some tpu: ThirdPartyUser | some t: Time | makeRequest[iu, tpu, t])
	(some dr: DataRequest | some tpu: ThirdPartyUser | some t: Time | approveDataRequest[tpu, dr, t])
	(some sdr: StoredDataRequest | some tpu: ThirdPartyUser | some t: Time | denyStoredDataRequest[tpu, sdr, t])
	(some sr: SubscriptionRequest | some tpu: ThirdPartyUser | some t: Time | denySubscriptionApproval[tpu, sr, t])
}


/*Run
***************************************************************************************************************************************/

run makeRequest for 10
run approveDataRequest for 10
run denyStoredDataRequest for 10
run denySubscriptionApproval for 10 

run show for 8 but exactly 4 Time


