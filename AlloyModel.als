
open util/boolean

//SIGNATURE

abstract sig User{
	name: one Stringa,
	surname: one Stringa,
	email: one Stringa,
	password: one Stringa,
	cf: one Stringa,
	dateOfBirth: one Stringa,
	birthPlace: one Stringa,
	telephoneNumber: lone Stringa,
	myReservations: set Reservation,
	myRides: set Ride,
}

sig Stringa{
}

sig Customer extends User{
	accountNumber: one Int,
}{ accountNumber>0}

sig Driver extends User{
	isAvailable: one Bool,
	taxiCode: one Int,
	taxiLicense: one Stringa,
	currentArea: one Area,
}{taxiCode>0} 

abstract sig Request{
	completed: one Bool,
	passenger: one Customer,
	cabman: one Driver,
	relatedQueue: one Queue,
	origin: one Stringa,
	id: one Stringa,
	initTime: one Int,
	finishTime: one Int,
}{ initTime>0 and finishTime>initTime}

sig Ride extends Request {
	waitTime: one Stringa,
}

sig Reservation extends Request{
	destination: one Stringa,
	date: one Stringa,
}

abstract sig City{
	serialNumber: one Stringa,
	areas: set Area,
}

sig Area{
	identification: one Stringa,
	drivers: set Driver,
	queues: set Queue,
	cityBelonging: one City,
}

sig Queue{
	location: one Area,
	driversOnQueue: some Driver,
	request: one Request,
}

//FACTS

fact UniqueUser {
	no u1, u2: User | (u1!=u2 and u1.cf=u2.cf and u1.email=u2.email)
}

fact UniqueCustomerIdentifier {
	all c1, c2: Customer | (c1!=c2 implies c1.accountNumber=c2.accountNumber)
}

fact UniqueIDRequest{
	no r1, r2: Request | (r1!=r2 and r1.id=r2.id)
}

fact UniqueRequestForQueue{
	all r1, r2: Request | (r1!=r2 implies r1.relatedQueue!=r2.relatedQueue)
} 

fact UniqueDriver {
	no d1, d2: Driver | (d1!=d2 and d1.taxiCode=d2.taxiCode and d1.taxiLicense=d2.taxiLicense)
}

fact CorrispondenceQueueArea{
	all q: Queue | all a: Area | (q.location= a iff (a.queues & q) =q)
}

fact UniqueQueuePerRequest{
	all q1, q2: Queue | (q1!=q2 implies q1.request!=q2.request)
}

fact CorrespondenceQueueRequest{
	all q: Queue | all r: Request | (q.request = r iff r.relatedQueue= q)
}

fact UniqueCitySerialNumber{
	no c1, c2: City | (c1!=c2 and c1.serialNumber=c2.serialNumber)
}

fact UniqueAreaId{
	all a1,a2: Area | (a1!=a2 implies a1.identification!=a2.identification)
}

fact DriversAvailableInQueue{
	all q : Queue | all dr : Driver | all r : Request |
 (dr.myReservations + dr.myRides)&q.request = r implies (q.driversOnQueue & dr) = dr
}

fact NoRequestOverlapping{
	all u: User | (all r1, r2 : u.myRides+u.myReservations | r1!=r2 implies
	(r1.finishTime<r2.initTime or r2.finishTime<r1.initTime))

}

fact CorrespondenceUserRequest{
	all r: Request | all c: Customer | (r.passenger=c implies (c.myRides+c.myReservations)&r=r)
	all r: Request | all dr: Driver | (r.cabman=dr implies (dr.myRides+dr.myReservations)&r=r)
}

fact AreaBelongsToOneCity{
	all a: Area | all c: City | (a.cityBelonging=c iff (c.areas)&a = a)
}


fact DriverHasAtLeastOneRide{
	all dr: Driver | (all r1, r2 :  dr.myRides| r1!=r2 implies (not(r1.completed=False and r2.completed=False)))
}

fact CustomerHasAtLeastOneRide{
	all c :Customer | (all r1, r2 :  c.myRides| r1!=r2 implies(not(r1.completed=False and r2.completed=False)))
	
}

fact DriverNotAvailable{
	all dr : Driver | all r : dr.myRides+dr.myReservations | (r.completed=False implies dr.isAvailable=False)
}

fact CustomerTakeAtLeastOneRequest{
	all c: Customer | (all req1, req2 : c.myReservations| (req1.completed=False and req2.completed=False) implies req1=req2)
}

//ASSERTIONS

assert driverUnavailableDuringRide{
	all r : Request | r.completed= False implies r.cabman.isAvailable= False
}

assert driverInQueueAndInArea{
	all q :Queue | all dr : Queue.driversOnQueue | dr.currentArea= q.location
}

assert NoTemporalyContraddiciton{
	no r : Request | (r.initTime> r.finishTime)
}

assert noTwoRideActiveForDriver{
	all r1,r2 : Ride | ((r1.completed=False and r2.completed=False and r1!=r2) implies r1.cabman!=r2.cabman)
}

assert noTwoCustomerInTheSameRide{
	all r1, r2 : Ride | r1!=r2 implies r1.passenger!=r2.passenger
}


 
pred show(){
	#Area =2
	#City = 2
	#Queue =6
	#Ride = 3
	#Reservation = 3
}

run show for 10
