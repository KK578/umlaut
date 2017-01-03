const SmtClass = require('./class.js');

module.exports = (uml) => {
	const classes = {};

	Object.keys(uml).forEach((className) => {
		classes[className] = new SmtClass(uml[className]);
	});

	return classes;
};
