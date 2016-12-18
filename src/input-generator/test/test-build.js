const path = require('path');

const SmtClass = require('../util/class.js');
const data = require('./test-data.json');

const smt = new SmtClass(data);

smt.writeSMT(path.join(__dirname, '../build/'));
