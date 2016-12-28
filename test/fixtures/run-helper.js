const path = require('path');
const yeoman = require('yeoman-environment');
const env = yeoman.createEnv();

env.lookup(() => {
	env.run('model-driven-testing:helper', {
		model: JSON.stringify(require('./inputs/SimpleMath.json'))
	});
});
