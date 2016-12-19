const SmtClass = require('./class.js');

module.exports = (uml) => {
	// TODO: Support multiple classes here.
	return new SmtClass(uml);
};
