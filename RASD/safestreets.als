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
one sig Pending extends Status {}{} --if no Authority checks this report 
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

-- a report send from a citizen must be in is report sended set
fact EqualityCitizen {
    all r: Report, c: Citizen| r.sender = c iff r in c.reportsSended
}

-- a report checked by an authority must be in is report checked set
fact EqualityAuthority {
    all r: Report, a: Authority | r.checker = a iff r in a.reportsChecked
}

-- if a report state is pending then it can't be in some authorities checked set
fact ReportCanOnlyBeEvaluatedByAuthority {
    all r: Report, a: Authority |   (r.status = Pending) 
                                        implies
                                    (r not in a.reportsChecked)
}

--All fiscalcode have to be associated to Citizen 
fact FiscalCodeCitizen {
    all fc: FiscalCode | some c: Citizen | fc in c.fiscalCode 
}

--All matricola have to be associated to Authority 
fact MatricolaAuthority {
    all m: Matricola | some a: Authority | m in a.matricola 
}

-- All registration have to be associated to User
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

pred sendReport [c, c1: Citizen, r: Report] {
    r.status = Pending
    r.sender = c
    c1.reportsSended = c.reportsSended + r
}

pred confirmReport [r, r1: Report, a, a1: Authority] {
    r1.sender = r.sender
    r1.status = Yes
    a1.reportsChecked = a.reportsChecked + r1
}

pred discardReport [r, r1: Report, a, a1: Authority] {
    r1.sender = r.sender
    r1.status = No
    a1.reportsChecked = a.reportsChecked + r1
}



pred show {
    #Citizen > 1
    #Authority > 1
    #Report > 2
}

run predicate sendReport for 4
--run predicate confirmReport for 5
--run predicate discardReport for 3
--run show for 5