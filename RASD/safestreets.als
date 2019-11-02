
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

sig Date {}
sig Time {}
sig License {}
sig Type {} 

sig Violation {
    location: one Location,
    date: one Date,
    time: one Time,
    license: one License,
    type: one Type
}

abstract sig Status {}
sig Pending extends Status {} --if no Authority checks this report 
sig Yes extends Status {} --if it's evaluated as an effective violation
sig No extends Status {} --if it isn't evaluated as an effective violation  

abstract sig Report {
    violation: one Violation,
    status: one Status,
    sender: one Citizen
}



--All Citizen have to be associated to a report 
fact ReportsToCitizen {
    all r: Report | some c: Citizen | (r.sender = c) && (r in c.reportsSended) 
    
}

fact ReportCanOnlyBeEvaluatedByAuthority {
    no disj r: Report, a: Authority | (r.status = Pending)
                                && (r in a.reportsChecked)
}

fact NoMultipleReportChecker {
    no disj a1,a2: Authority, r: Report | 
                (r in a1.reportsChecked) &&
                (r in a2.reportsChecked)  
}

--Every Citzen has different report sended set
--fact NoSameSender {
--    no disj c1, c2 :Citizen | c1.reportSended = c2.reportSended
--}



--All Authorities have to be associated to a report 
--fact ReportsToAuthority {
--    all a: Authority | some r: Report | r in a.reportChecked 
--}

--Every Report has different report checked set
--fact NoSameChecker {
 --   no disj a1, a2 :Authority | a1.reportChecked = a2.reportChecked
--}


--{latitude >= -90 and latitude <= 90 and longitude >= -180 and longitude <= 180 }




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


--All Location have to be associated to a Violation 
fact LocationViolation {
    all l: Location | some v: Violation | l in v.location
}

--All time have to be associated to a Violation 
fact TimeViolation {
    all t: Time | some v: Violation | t in v.time
}

--All Date have to be associated to a Violation 
fact DateViolation {
    all d: Date | some v: Violation | d in v.date
}

--All LicensePlate have to be associated to a Violation 
fact LicenseViolation {
    all lp: License | some v: Violation | lp in v.license
}

--All Type have to be associated to a Violation 
fact TypeViolation {
    all t: Type | some v: Violation | t in v.type
}

--indicate the report status, 


--All violations have to be associated to a Report 
--fact ViolationToReport {
 --   all v: Violation | some r: Report | v in r.violation 
--}

--Every Report has different violation
fact NoSameViolation {
    no disj r1, r2 :Report | r1.violation = r2.violation
}

--All Citizen have to be associated to a report 
--fact CitizenToReport {
  --  all c: Citizen | some r: Report | c in r.sender 
--}

--Every Report has different sender
--fact NoSameSender {
  --  no disj r1, r2 :Report | r1.sender = r2.sender
--}

--All Status have to be associated to a report 
--fact StatusToReport {
 --   all s: Status | some r: Report | s in r.status 
--}

--cannot exists report checked by an authority with a pending status
--fact NoPendingReportChecked {
  --  all a: Authority, r: Report | r in a.reportChecked implies r.status != Pending 
--}

--a report can't be evaluated by two different authorities
--fact NoTwoRetriviedReportsCheckedByOneAuthority {
  --  all r: Report, a1, a2: Authority | 
     --   ( r in a1.reportChecked implies r not in a2.reportChecked)
--}

-- cannot exists two reports made by the same Citizen with the same violation
fact NoSameReport {
    no disj r1,r2: Report | (r1.sender = r2.sender) && (r1.violation = r2.violation) 

}

fact EualityCitizen {
    all r: Report, c: Citizen| r.sender = c iff r in c.reportsSended
}

--fact NoYesOrNoReportToCitizen {
  --  all c: Citizen, r: Report | r in c.reportSended implies r.status = Pending
--}
pred sendReport [c, c1: Citizen, r: Report, v: Violation] {
    r.violation = v
    r.status = Pending
    r.sender = c
    c1.reportsSended = c.reportsSended + r
}

pred confirmReport [r, r1: Report, a, a1: Authority] {
    r1.violation = r.violation
    r1.sender = r.sender
    r1.status = Yes
    a1.reportsChecked = a.reportsChecked + r1
}

pred discardReport [r, r1: Report, a, a1: Authority] {
    r1.violation = r.violation
    r1.sender = r.sender
    r1.status = No
    a1.reportsChecked = a.reportsChecked + r1
}


pred show {
    #Citizen > 1
    #Authority > 1
    #Report > 1
}

--run discardReport
run show for 5