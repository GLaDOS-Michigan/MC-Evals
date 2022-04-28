include "types.dfy"

module Network {
import opened Types

datatype IoOpt = None | Some(p:Packet)

datatype EnvStep = 
    IoStep(actor:Id, recvIo:IoOpt, sendIo:IoOpt)

datatype Environment = Env(
        sentPackets:set<Packet>,
        nextStep:EnvStep
    )

predicate EnvironmentInit(e:Environment) {
    e.sentPackets == {}
}

predicate ValidIoStep(iostep:EnvStep) 
    requires iostep.IoStep?
{
    && (iostep.recvIo.Some? ==> iostep.recvIo.p.dst == iostep.actor)
    && (iostep.sendIo.Some? ==> iostep.sendIo.p.src == iostep.actor)
}


predicate EnvironmentNext(e:Environment, e':Environment)
{
    var actor, recvIo, sendIo := e.nextStep.actor, e.nextStep.recvIo, e.nextStep.sendIo;
    && ValidIoStep(e.nextStep)
    // Bug 3: The line "recvIo.Some? ==> recvIo.p in e.sentPackets" wasn't parenthesised
    // leading to a bad parsing 
    && (recvIo.Some? ==> recvIo.p in e.sentPackets)
    &&  match sendIo {
        case Some(p) => e'.sentPackets == e.sentPackets + {p}
        case None => e'.sentPackets == e.sentPackets
    }
}
}