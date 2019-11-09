sig FiscalCode {}
sig Matricola {}
sig Email {}
sig Password {}

sig Registration {
    email: one Email,
    password: one Password
}

abstract sig User {
    registration: one Registration
}

sig Citizen extends User {
    fiscalCode: one FiscalCode,
    reportsSended: set Report
}

sig Authority extends User {
    matricola: one Matricola,
    reportsChecked: set Report
}

sig Location {
    latitude: one Int, 
    longitude: one Int
} {latitude >= -3 and latitude <= 3 and longitude >= -6 and longitude <= 6 }

abstract sig Status {}
one sig Pending extends Status {} --if no Authority checks this report 
one sig Yes extends Status {} --if it's evaluated as an effective violation
one sig No extends Status {} --if it isn't evaluated as an effective violation  

sig Date {}
sig Time {}
sig License {}
sig Type {}

abstract sig Report {
    location: one Location,
    date: one Date,
    time: one Time,
    license: one License,
    type: one Type,
    status: one Status,
    sender: one Citizen,
    checker: one Authority
}

-------------------- FACTS --------------------

--A report send from a citizen must be in is report sended set
fact EqualityCitizen {
    all r: Report | some c: Citizen| r.sender = c iff r in c.reportsSended
}

--A report checked by an authority must be in is report checked set
fact EqualityAuthority {
    all r: Report | some a: Authority | r.checker = a iff r in a.reportsChecked
}

--No reports with state pending in some authority's checked set
fact NoAuthorityWithPendingReportsInChecked {
    no r: Report | some a: Authority |
        r in a.reportsChecked and r.status = Pending and r.checker = a
}

--If a report is checked must be in one authority checked set 
fact ReportInCheckedSet {
    all r: Report | some a: Authority | 
        r.status != Pending implies (r in a.reportsChecked and r.checker = a)
}

--If a report exists must be sended by a citizen
fact ReportInSendedSet {
    all r: Report | some c: Citizen | r.sender = c and r in c.reportsSended
}

--All fiscal code have to be associated to Citizen 
fact FiscalCodeCitizen {
    all fc: FiscalCode | some c: Citizen | fc in c.fiscalCode 
}

--All matricola have to be associated to Authority 
fact MatricolaAuthority {
    all m: Matricola | some a: Authority | m in a.matricola 
}

--All registration have to be associated to User
fact RegistrationUser {
  all r: Registration | some u: User | r in u.registration
}

--All email have to be associated to a User Registration
fact EmailRegistration {
    all e : Email | some u: User | e in u.registration.email
}

--All password have to be associated to a User Registration
fact PassRegistration {
    all p : Password | some u: User| p in u.registration.password
}

--Every User has different email
fact NoSameEmail {
    no disj u1, u2 :User | u1.registration.email = u2.registration.email
}

--Every Citizen has different FiscalCode
fact NoSameFiscalCode {
    no disj c1, c2 : Citizen | c1.fiscalCode = c2.fiscalCode
}

--Every Authority has different Matricola
fact NoSameAuthority {
    no disj a1, a2 : Authority | a1.matricola = a2.matricola
}

--If a report is evaluated than the status isn't pending
fact ReportInAuthoritySetsMustBeChecked {
    some r: Report | one a: Authority | r in a.reportsChecked 
                                and ((r.status = Yes)
                                        or
                                    (r.status = No)) 
}

--All the citizens can't have some equal report in their sets
fact OnlyDisjointedReportsSet {
    no r: Report | all c1,c2: Citizen |
    (r in c1.reportsSended) and (r in c2.reportsSended) 
}

-------------------- ASSERTS --------------------

--If a report state is pending then it can't be in some authorities checked set
assert ReportCanOnlyBeEvaluatedByAuthority {
    some r: Report | one a: Authority | (r.status = Pending) 
                                        implies 
                                    (r not in a.reportsChecked)
}

-------------------- CHECKS --------------------
check ReportCanOnlyBeEvaluatedByAuthority

-------------------- PREDICATES --------------------

pred sendReport [c, c1: Citizen, r: Report] {
    c.registration = c1.registration
    c.fiscalCode = c1.fiscalCode
    r.status = Pending
    r.sender = c
    c1.reportsSended = c.reportsSended + r
}

pred confirmReport [r, r1: Report, a, a1: Authority] {
    a.matricola = a1.matricola
    r.status = Pending
    r1.sender = r.sender
    r1.status = Yes
    a1.reportsChecked = a.reportsChecked + r1
}

pred discardReport [r, r1: Report, a, a1: Authority] {
    a.matricola = a1.matricola
    r.status = Pending
    r1.sender = r.sender
    r1.status = No
    a1.reportsChecked = a.reportsChecked + r1
}

pred world1 {
    #Citizen > 1
    #Authority > 1
    #Report > 2
}

pred world2 {
    #Citizen = 3
    #Authority = 3
    #Report = 3
}

-------------------- RUNS --------------------

run sendReport for 4
run confirmReport for 5
run discardReport for 5
run world1 for 5
run world2 for 7