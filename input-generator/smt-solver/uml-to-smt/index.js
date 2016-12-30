const SmtClass = require('./class.js');

module.exports = (uml) => {
	return Object.keys(uml).reduce((previous, current) => {
		const smtClass = new SmtClass(uml[current]);

		previous[current] = smtClass;

		return previous;
	}, {});
};
