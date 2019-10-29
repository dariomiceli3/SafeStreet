sig FiscalCode {}
sig Matricola {}
sig Email {}
sig Password {}
sig Registration {
    email: one Email,
    Password: one Password
}

abstract sig User {
    registration: one registration
}

sig Citizen extends User {
    fiscalCode: one FiscalCode
}

sig Authority extends Authority {
    matricola: one Matricola
}

sig Location {
    latitude: one int,
    longitude: one int
}

sig Date {}
sig Time {}

sig Violation {
    location: one Location,
    date: one Date,
    time: one Time
}
