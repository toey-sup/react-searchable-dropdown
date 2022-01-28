import React, { memo } from 'react';
import Tooltip from '@material-ui/core/Tooltip';
import Typography from '@material-ui/core/Typography';

export interface Choice {
  label: string;
  used?: boolean;
  description?: string;
  [key: string]: any;
}

export interface ChoiceSection {
  choices: Choice[];
  sectionName?: string;
  sectionPrefix?: string;
}

export interface Props {
  choice: Choice;
  id?: string;
  className?: string;
  handleSelect: (choice: Choice) => void;
}

const SelectorItem: React.FC<Props> = memo(({ choice, id, className, handleSelect }) => {
  return (
    <Tooltip
      title={<Typography style={{ whiteSpace: 'pre-line' }}>{choice?.description}</Typography>}
      key={`${choice?.sectionPrefix || ''} ${choice?.label}`}
      enterDelay={300}
      leaveDelay={0}
      enterNextDelay={200}
      interactive
      placement="right-start"
      arrow
      disableHoverListener={!choice?.description}
    >
      <div
        key={choice?.fieldName || choice?.label}
        className={`flex h-full px-4 ${
          choice?.used ? 'text-gray-300 cursor-default' : 'cursor-pointer hover:bg-gray-200'
        } ${className}`}
        onClick={() => {
          if (!choice?.used) handleSelect(choice);
        }}
        id={`${id}-${choice?.label}`}
        aria-hidden="true"
      >
        <Typography className="flex items-center">{choice?.label}</Typography>
      </div>
    </Tooltip>
  );
});

export default SelectorItem;
