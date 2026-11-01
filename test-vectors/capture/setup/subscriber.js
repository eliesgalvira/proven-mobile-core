db = db.getSiblingDB('open5gs');
db.subscribers.deleteMany({imsi: '001010000000001'});
db.subscribers.insertOne({
  schema_version: 1,
  imsi: '001010000000001',
  msisdn: [], imeisv: [], mme_host: [], mme_realm: [], purge_flag: [],
  security: {k: '465B5CE8B199B49FAA5F0A2EE238A6BC', op: null,
             opc: 'E8ED289DEBA952E4283B54E88E6183CA', amf: '8000', sqn: NumberLong(64)},
  ambr: {downlink: {value: 1, unit: 3}, uplink: {value: 1, unit: 3}},
  slice: [{sst: 1, default_indicator: true, session: [{
    name: 'internet', type: 1,
    qos: {index: 9, arp: {priority_level: 8, pre_emption_capability: 1, pre_emption_vulnerability: 1}},
    ambr: {downlink: {value: 1, unit: 3}, uplink: {value: 1, unit: 3}},
    pcc_rule: []}]}],
  access_restriction_data: 32, subscriber_status: 0, operator_determined_barring: 0,
  network_access_mode: 0, subscribed_rau_tau_timer: 12, __v: 0
});
printjson(db.subscribers.findOne({imsi: '001010000000001'}, {security: 1}));
