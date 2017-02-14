using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace UmlAnnotator
{
	public class LinkedOclCondition : OclCondition
	{
		private static string ConvertString(string condition)
		{
			string result = condition;

			// Linked conditions will be present at the start of the condition string, after the '('.
			// Contained within a { } pair of curly braces.
			if (result[1] == '{')
			{
				result = result.Remove(1, result.IndexOf('}') + 1);
			}

			return result;
		}

		public List<OclCondition> LinkedConditions;
		private List<OclCondition> preconditions;

		public LinkedOclCondition(List<OclCondition> preconditions) : base()
		{
			LinkedConditions = new List<OclCondition>();
			this.preconditions = preconditions;
		}

		public LinkedOclCondition(List<OclCondition> preconditions, string condition) : base(ConvertString(condition))
		{
			LinkedConditions = new List<OclCondition>();
			this.preconditions = preconditions;

			if (condition[1] == '{')
			{
				string storedLink = condition.Substring(1, condition.IndexOf('}'));
			}
		}

		public override string ToString()
		{
			string baseString = base.ToString();
			string list = "";
			string linkedString = "";
			for (int i = 0; i < preconditions.Count; i++)
			{
				if (LinkedConditions.Contains(preconditions[i]))
				{
					list += i + ";";
				}
			}

			if (list.Length > 0)
			{
				// Remove the last ';'.
				list = list.Remove(list.Length - 1);
				linkedString = "{" + list + "} ";
			}

			string result = baseString.Insert(1, linkedString);

			return result;
		}
	}
}
